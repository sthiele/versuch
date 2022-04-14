pub mod convert;
pub mod solver;

use thiserror::Error;

#[derive(Error, Debug)]
pub enum AspifError {
    #[error("More than one solve item")]
    MultipleSolveItems,
    #[error("No solve item")]
    NoSolveItem,
    #[error("ParseError: {msg}")]
    ParseError { msg: String },
}
