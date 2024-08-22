
use std::collections::VecDeque;
use std::fmt;
use sqlparser::keywords::STREAM;
#[warn(unused_imports)]
use sqlparser::{
    ast::{
        ColumnDef, ColumnOptionDef, Expr, ObjectName, OrderByExpr, Query, Setting, Statement as SQLStatement,
         TableConstraint, Value, Ident, TableEngine, OneOrManyWithParens, CommentDef
    },
    dialect::{keywords::Keyword, ClickHouseDialect, Dialect, GenericDialect},
    parser::{Parser, ParserError},
    tokenizer::{Token, TokenWithLocation, Tokenizer, Word},
};



// Use `Parser::expected` instead, if possible
macro_rules! parser_err {
    ($MSG:expr) => {
        Err(ParserError::ParserError($MSG.to_string()))
    };
}

fn parse_file_type(s: &str) -> Result<String, ParserError> {
    Ok(s.to_uppercase())
}


/// This type defines a lexicographical ordering.
pub(crate) type LexOrdering = Vec<OrderByExpr>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(self) enum StreamType {
    DEFAULT,
    RANDOM,
    EXTERNAL,
    MUTABLE
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CreateStream {
    /// Stream name
    pub name: String,
    /// Optional schema
    pub columns: Vec<ColumnDef>,
    /// File type (Parquet, NDJSON, CSV, etc)
    pub file_type: String,
    /// Path to file
    pub location: String,
    /// Partition Columns
    pub partition_cols: Vec<String>,
    /// Ordered expressions
    pub order_exprs: Vec<LexOrdering>,
    /// Option to not error if table already exists
    pub if_not_exists: bool,
    /// Table(provider) specific options
    pub settings: Vec<Setting>,
    /// A table-level constraint
    pub constraints: Vec<TableConstraint>,
    /// Primary key
    pub primary_key: Option<Box<Expr>>,
    /// Comment
    pub stream_type: StreamType,
}

impl fmt::Display for CreateStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "CREATE STREAM ")?;
        if self.if_not_exists {
            write!(f, "IF NOT EXISTS ")?;
        }
        write!(f, "{} ", self.name)?;
        write!(f, "STORED AS {} ", self.file_type)?;
        write!(f, "LOCATION {} ", self.location)
    }
}

/// Timeplus SQL Statement.
///
/// This can either be a [`Statement`] from [`sqlparser`] from a
/// standard SQL dialect, or a DataFusion extension such as `CREATE
/// EXTERNAL TABLE`. See [`DFParser`] for more information.
///
/// [`Statement`]: sqlparser::ast::Statement
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
    /// ANSI SQL AST node (from sqlparser-rs)
    Statement(Box<SQLStatement>),
    /// Extension: `CREATE EXTERNAL TABLE`
    CreateStream(CreateStream),
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Statement(stmt) => write!(f, "{stmt}"),
            Statement::CreateStream(stmt) => write!(f, "{stmt}"),
        }
    }
}

fn ensure_not_set<T>(field: &Option<T>, name: &str) -> Result<(), ParserError> {
    if field.is_some() {
        return Err(ParserError::ParserError(format!(
            "{name} specified more than once",
        )));
    }
    Ok(())
}






#[derive(Debug)]
pub struct TimeplusDialect {}

impl Dialect for TimeplusDialect {
    fn is_identifier_start(&self, ch: char) -> bool {
        ch.is_ascii_lowercase() || ch.is_ascii_uppercase() || ch == '_'
    }

    fn is_identifier_part(&self, ch: char) -> bool {
        self.is_identifier_start(ch) || ch.is_ascii_digit()
    }

    fn supports_string_literal_backslash_escape(&self) -> bool {
        true
    }

    fn supports_select_wildcard_except(&self) -> bool {
        true
    }

    fn describe_requires_table_keyword(&self) -> bool {
        false
    }
}



/// DataFusion SQL Parser based on [`sqlparser`]
///
/// Parses DataFusion's SQL dialect, often delegating to [`sqlparser`]'s [`Parser`].
///
/// DataFusion mostly follows existing SQL dialects via
/// `sqlparser`. However, certain statements such as `COPY` and
/// `CREATE EXTERNAL TABLE` have special syntax in DataFusion. See
/// [`Statement`] for a list of this special syntax
pub struct TPParser<'a> {
    pub parser: Parser<'a>,
}

impl<'a> TPParser<'a> {
    /// Create a new parser for the specified tokens using the
    /// [`ClickHouseDialect`].
    pub fn new(sql: &str) -> Result<Self, ParserError> {
        let dialect = &ClickHouseDialect {};
        TPParser::new_with_dialect(sql, dialect)
    }

    /// Create a new parser for the specified tokens with the
    /// specified dialect.
    pub fn new_with_dialect(
        sql: &str,
        dialect: &'a dyn Dialect,
    ) -> Result<Self, ParserError> {
        let mut tokenizer = Tokenizer::new(dialect, sql);
        let tokens = tokenizer.tokenize()?;

        Ok(TPParser {
            parser: Parser::new(dialect).with_tokens(tokens),
        })
    }

    /// Parse a sql string into one or [`Statement`]s using the
    /// [`GenericDialect`].
    pub fn parse_sql(sql: &str) -> Result<VecDeque<Statement>, ParserError> {
        let dialect = &GenericDialect {};
        TPParser::parse_sql_with_dialect(sql, dialect)
    }

    /// Parse a SQL string and produce one or more [`Statement`]s with
    /// with the specified dialect.
    pub fn parse_sql_with_dialect(
        sql: &str,
        dialect: &dyn Dialect,
    ) -> Result<VecDeque<Statement>, ParserError> {
        let mut parser = TPParser::new_with_dialect(sql, dialect)?;
        let mut stmts = VecDeque::new();
        let mut expecting_statement_delimiter = false;
        loop {
            // ignore empty statements (between successive statement delimiters)
            while parser.parser.consume_token(&Token::SemiColon) {
                expecting_statement_delimiter = false;
            }

            if parser.parser.peek_token() == Token::EOF {
                break;
            }
            if expecting_statement_delimiter {
                return parser.expected("end of statement", parser.parser.peek_token());
            }

            let statement = parser.parse_statement()?;
            stmts.push_back(statement);
            expecting_statement_delimiter = true;
        }
        Ok(stmts)
    }

    pub fn parse_sql_into_expr_with_dialect(
        sql: &str,
        dialect: &dyn Dialect,
    ) -> Result<Expr, ParserError> {
        let mut parser = TPParser::new_with_dialect(sql, dialect)?;
        parser.parse_expr()
    }

    /// Report an unexpected token
    fn expected<T>(
        &self,
        expected: &str,
        found: TokenWithLocation,
    ) -> Result<T, ParserError> {
        parser_err!(format!("Expected {expected}, found: {found}"))
    }

    /// Parse a new expression
    pub fn parse_statement(&mut self) -> Result<Statement, ParserError> {
        match self.parser.peek_token().token {
            Token::Word(w) => {
                match w.keyword {
                    Keyword::CREATE => {
                        self.parser.next_token();
                        self.parse_create()
                    }
                    _ => {
                        // use sqlparser-rs parser
                        Ok(Statement::Statement(Box::from(
                            self.parser.parse_statement()?,
                        )))
                    }
                }
            }
            _ => {
                // use the native parser
                Ok(Statement::Statement(Box::from(
                    self.parser.parse_statement()?,
                )))
            }
        }
    }

    pub fn parse_expr(&mut self) -> Result<Expr, ParserError> {
        if let Token::Word(w) = self.parser.peek_token().token {
            match w.keyword {
                Keyword::CREATE  => {
                    return parser_err!("Unsupported command in expression");
                }
                _ => {}
            }
        }

        self.parser.parse_expr()
    }

    /// Parse the next token as a key name for an option list
    ///
    /// Note this is different than [`parse_literal_string`]
    /// because it allows keywords as well as other non words
    ///
    /// [`parse_literal_string`]: sqlparser::parser::Parser::parse_literal_string
    pub fn parse_option_key(&mut self) -> Result<String, ParserError> {
        let next_token = self.parser.next_token();
        match next_token.token {
            Token::Word(Word { value, .. }) => {
                let mut parts = vec![value];
                while self.parser.consume_token(&Token::Period) {
                    let next_token = self.parser.next_token();
                    if let Token::Word(Word { value, .. }) = next_token.token {
                        parts.push(value);
                    } else {
                        // Unquoted namespaced keys have to conform to the syntax
                        // "<WORD>[\.<WORD>]*". If we have a key that breaks this
                        // pattern, error out:
                        return self.parser.expected("key name", next_token);
                    }
                }
                Ok(parts.join("."))
            }
            Token::SingleQuotedString(s) => Ok(s),
            Token::DoubleQuotedString(s) => Ok(s),
            Token::EscapedStringLiteral(s) => Ok(s),
            _ => self.parser.expected("key name", next_token),
        }
    }

    /// Parse the next token as a value for an option list
    ///
    /// Note this is different than [`parse_value`] as it allows any
    /// word or keyword in this location.
    ///
    /// [`parse_value`]: sqlparser::parser::Parser::parse_value
    pub fn parse_option_value(&mut self) -> Result<Value, ParserError> {
        let next_token = self.parser.next_token();
        match next_token.token {
            // e.g. things like "snappy" or "gzip" that may be keywords
            Token::Word(word) => Ok(Value::SingleQuotedString(word.value)),
            Token::SingleQuotedString(s) => Ok(Value::SingleQuotedString(s)),
            Token::DoubleQuotedString(s) => Ok(Value::DoubleQuotedString(s)),
            Token::EscapedStringLiteral(s) => Ok(Value::EscapedStringLiteral(s)),
            Token::Number(n, l) => Ok(Value::Number(n, l)),
            _ => self.parser.expected("string or numeric value", next_token),
        }
    }


    /// Parse a SQL `CREATE` statement handling `CREATE EXTERNAL TABLE`
    pub fn parse_create(&mut self) -> Result<Statement, ParserError> {
        if self.parser.parse_keyword(Keyword::STREAM) {
            self.parse_create_stream()
        }
        else if self.parser.parse_keyword(Keyword::EXTERNAL) {
            self.parser.expect_keyword(Keyword::STREAM);
            let create = self.parse_create_stream();
            if let Ok(Statement::CreateStream(mut create_)) = create {
                create_.stream_type = StreamType::EXTERNAL;
                return Ok(Statement::CreateStream(create_));
            }else {
                return create;
            }
        }
        else if self.parser.parse_keyword(Keyword::RANDOM) {
            self.parser.expect_keyword(Keyword::STREAM);
            let create = self.parse_create_stream();
            if let Ok(Statement::CreateStream(mut create_)) = create {
                create_.stream_type = StreamType::RANDOM;
                return Ok(Statement::CreateStream(create_));
            }else {
                return create;
            }
        }
        else if self.parser.parse_keyword(Keyword::MUTABLE) {
            self.parser.expect_keyword(Keyword::STREAM);
            let create = self.parse_create_stream();
            if let Ok(Statement::CreateStream(mut create_)) = create {
                create_.stream_type = StreamType::MUTABLE;
                return Ok(Statement::CreateStream(create_));
            }else {
                return create;
            }
        }
        else {
            Ok(Statement::Statement(Box::from(self.parser.parse_create()?)))
        }
    }

    fn parse_partitions(&mut self) -> Result<Vec<String>, ParserError> {
        let mut partitions: Vec<String> = vec![];
        if !self.parser.consume_token(&Token::LParen)
            || self.parser.consume_token(&Token::RParen)
        {
            return Ok(partitions);
        }

        loop {
            if let Token::Word(_) = self.parser.peek_token().token {
                let identifier = self.parser.parse_identifier(false)?;
                partitions.push(identifier.to_string());
            } else {
                return self.expected("partition name", self.parser.peek_token());
            }
            let comma = self.parser.consume_token(&Token::Comma);
            if self.parser.consume_token(&Token::RParen) {
                // allow a trailing comma, even though it's not in standard
                break;
            } else if !comma {
                return self.expected(
                    "',' or ')' after partition definition",
                    self.parser.peek_token(),
                );
            }
        }
        Ok(partitions)
    }

    /// Parse the ordering clause of a `CREATE EXTERNAL TABLE` SQL statement
    pub fn parse_order_by_exprs(&mut self) -> Result<Vec<OrderByExpr>, ParserError> {
        let mut values = vec![];
        self.parser.expect_token(&Token::LParen)?;
        loop {
            values.push(self.parse_order_by_expr()?);
            if !self.parser.consume_token(&Token::Comma) {
                self.parser.expect_token(&Token::RParen)?;
                return Ok(values);
            }
        }
    }

    /// Parse an ORDER BY sub-expression optionally followed by ASC or DESC.
    pub fn parse_order_by_expr(&mut self) -> Result<OrderByExpr, ParserError> {
        let expr = self.parser.parse_expr()?;

        let asc = if self.parser.parse_keyword(Keyword::ASC) {
            Some(true)
        } else if self.parser.parse_keyword(Keyword::DESC) {
            Some(false)
        } else {
            None
        };

        let nulls_first = if self
            .parser
            .parse_keywords(&[Keyword::NULLS, Keyword::FIRST])
        {
            Some(true)
        } else if self.parser.parse_keywords(&[Keyword::NULLS, Keyword::LAST]) {
            Some(false)
        } else {
            None
        };

        Ok(OrderByExpr {
            expr,
            asc,
            nulls_first,
            with_fill: None,
        })
    }

    // This is a copy of the equivalent implementation in sqlparser.
    fn parse_columns(
        &mut self,
    ) -> Result<(Vec<ColumnDef>, Vec<TableConstraint>), ParserError> {
        let mut columns = vec![];
        let mut constraints = vec![];
        if !self.parser.consume_token(&Token::LParen)
            || self.parser.consume_token(&Token::RParen)
        {
            return Ok((columns, constraints));
        }

        loop {
            if let Some(constraint) = self.parser.parse_optional_table_constraint()? {
                constraints.push(constraint);
            } else if let Token::Word(_) = self.parser.peek_token().token {
                let column_def = self.parse_column_def()?;
                columns.push(column_def);
            } else {
                return self.expected(
                    "column name or constraint definition",
                    self.parser.peek_token(),
                );
            }
            let comma = self.parser.consume_token(&Token::Comma);
            if self.parser.consume_token(&Token::RParen) {
                // allow a trailing comma, even though it's not in standard
                break;
            } else if !comma {
                return self.expected(
                    "',' or ')' after column definition",
                    self.parser.peek_token(),
                );
            }
        }

        Ok((columns, constraints))
    }

    fn parse_column_def(&mut self) -> Result<ColumnDef, ParserError> {
        let name = self.parser.parse_identifier(false)?;
        let data_type = self.parser.parse_data_type()?;
        let collation = if self.parser.parse_keyword(Keyword::COLLATE) {
            Some(self.parser.parse_object_name(false)?)
        } else {
            None
        };
        let mut options = vec![];
        loop {
            if self.parser.parse_keyword(Keyword::CONSTRAINT) {
                let name = Some(self.parser.parse_identifier(false)?);
                if let Some(option) = self.parser.parse_optional_column_option()? {
                    options.push(ColumnOptionDef { name, option });
                } else {
                    return self.expected(
                        "constraint details after CONSTRAINT <name>",
                        self.parser.peek_token(),
                    );
                }
            } else if let Some(option) = self.parser.parse_optional_column_option()? {
                options.push(ColumnOptionDef { name: None, option });
            } else {
                break;
            };
        }
        Ok(ColumnDef {
            name,
            data_type,
            collation,
            options,
        })
    }

    fn parse_create_stream(
        &mut self,
    ) -> Result<Statement, ParserError> {
        // self.parser.expect_keyword(Keyword::STREAM)?;
        let if_not_exists =
            self.parser
                .parse_keywords(&[Keyword::IF, Keyword::NOT, Keyword::EXISTS]);
        let stream_name = self.parser.parse_object_name(true)?;
        let (mut columns, constraints) = self.parse_columns()?;

        #[derive(Default)]
        struct Builder {
            file_type: Option<String>,
            location: Option<String>,
            table_partition_cols: Option<Vec<String>>,
            order_exprs: Vec<LexOrdering>,
            settings: Option<Vec<Setting>>,
            primary_key: Option<Box<Expr>>
        }
        let mut builder = Builder::default();

        loop {
            if let Some(keyword) = self.parser.parse_one_of_keywords(&[
                Keyword::LOCATION,
                Keyword::WITH,
                Keyword::DELIMITER,
                Keyword::COMPRESSION,
                Keyword::PARTITIONED,
                Keyword::SETTINGS,
                Keyword::PRIMARY,
            ]) {
                match keyword {
                    Keyword::WITH => {
                        if self.parser.parse_keyword(Keyword::ORDER) {
                            builder.order_exprs.push(self.parse_order_by_exprs()?);
                        } else {
                            self.parser.expect_keyword(Keyword::HEADER)?;
                            self.parser.expect_keyword(Keyword::ROW)?;
                            return parser_err!("WITH HEADER ROW clause is no longer in use. Please use the OPTIONS clause with 'format.has_header' set appropriately, e.g., OPTIONS (format.has_header true)");
                        }
                    }
                    Keyword::DELIMITER => {
                        return parser_err!("DELIMITER clause is no longer in use. Please use the OPTIONS clause with 'format.delimiter' set appropriately, e.g., OPTIONS (format.delimiter ',')");
                    }
                    Keyword::COMPRESSION => {
                        self.parser.expect_keyword(Keyword::TYPE)?;
                        return parser_err!("COMPRESSION TYPE clause is no longer in use. Please use the OPTIONS clause with 'format.compression' set appropriately, e.g., OPTIONS (format.compression gzip)");
                    }
                    Keyword::PARTITIONED => {
                        self.parser.expect_keyword(Keyword::BY)?;
                        ensure_not_set(&builder.table_partition_cols, "PARTITIONED BY")?;
                        // Expects either list of column names (col_name [, col_name]*)
                        // or list of column definitions (col_name datatype [, col_name datatype]* )
                        // use the token after the name to decide which parsing rule to use
                        // Note that mixing both names and definitions is not allowed
                        let peeked = self.parser.peek_nth_token(2);
                        if peeked == Token::Comma || peeked == Token::RParen {
                            // list of column names
                            builder.table_partition_cols = Some(self.parse_partitions()?)
                        } else {
                            // list of column defs
                            let (cols, cons) = self.parse_columns()?;
                            builder.table_partition_cols = Some(
                                cols.iter().map(|col| col.name.to_string()).collect(),
                            );

                            columns.extend(cols);

                            if !cons.is_empty() {
                                return Err(ParserError::ParserError(
                                    "Constraints on Partition Columns are not supported"
                                        .to_string(),
                                ));
                            }
                        }
                    }
                    Keyword::SETTINGS => {
                        ensure_not_set(&builder.settings, "SETTINGS")?;
                        builder.settings = self.parse_settings()?;
                    }
                    Keyword::PRIMARY => {
                        self.parser.expect_keyword(Keyword::KEY);
                        builder.primary_key = Some(Box::new(self.parse_expr()?))

                    }
                    _ => {
                        unreachable!()
                    }
                }
            } else {
                let token = self.parser.next_token();
                if token == Token::EOF || token == Token::SemiColon {
                    break;
                } else {
                    return Err(ParserError::ParserError(format!(
                        "Unexpected token {token}"
                    )));
                }
            }
        }

        // Validations: location and file_type are required

        let create = CreateStream {
            stream_type: StreamType::DEFAULT,
            name: stream_name.to_string(),
            columns,
            file_type: builder.file_type.unwrap_or(String::new()),
            location: builder.location.unwrap_or(String::new()),
            partition_cols: builder.table_partition_cols.unwrap_or(vec![]),
            order_exprs: builder.order_exprs,
            if_not_exists,
            settings: builder.settings.unwrap_or(Vec::new()),
            constraints,
            primary_key: builder.primary_key
        };
        Ok(Statement::CreateStream(create))
    }


    fn parse_settings(&mut self) -> Result<Option<Vec<Setting>>, ParserError> {
        let settings = {
            let key_values = self.parser.parse_comma_separated(|p| {
                let key = p.parse_identifier(false)?;
                p.expect_token(&Token::Eq)?;
                let value = p.parse_value()?;
                Ok(Setting { key, value })
            })?;
            Some(key_values)
        };
        Ok(settings)
    }
    fn parse_optional_on_cluster(&mut self) -> Result<Option<Ident>, ParserError> {
        if self.parser.parse_keywords(&[Keyword::ON, Keyword::CLUSTER]) {
            Ok(Some(self.parser.parse_identifier(false)?))
        } else {
            Ok(None)
        }
    }

    fn parse_parenthesized_identifiers(&mut self) -> Result<Vec<Ident>, ParserError> {
        self.parser.expect_token(&Token::LParen)?;
        let partitions = self.parser.parse_comma_separated(|p| p.parse_identifier(false))?;
        self.parser.expect_token(&Token::RParen)?;
        Ok(partitions)
    }
}

mod tests{
    use super::TPParser;

    #[test]
    fn test_create_stream(){
        let sql = "CREATE MUTABLE STREAM IF NOT EXISTS default.test_table (
            id INT,
            name VARCHAR(255),
            age INT,
            another_name uint64
        )
        PRIMARY KEY (id,name)
        PARTITIONED BY (year INT, month INT, day INT)
        SETTINGS a = \"good\"";
        let mut parser = TPParser::new(sql).unwrap();
        let statement = parser.parse_statement().unwrap();
        println!("{:?}", statement);
    }
}