//! CLI for producers/consumers

use clap::Parser;

#[derive(Parser)]
pub struct Cli {
    /// Number of producers
    #[arg(long, default_value = "1")]
    pub producers: usize,

    /// Number of consumers
    #[arg(long, default_value = "1")]
    pub consumers: usize,

    /// Buffer size
    #[arg(long, default_value = "1")]
    pub buffer_size: usize,
}
