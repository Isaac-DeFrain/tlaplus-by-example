//! CLI for Producers and Consumers Example

use clap::Parser;

#[derive(Parser)]
struct Cli {
    /// Number of producers
    #[arg(long, default_value = "1")]
    producers: usize,

    /// Number of consumers
    #[arg(long, default_value = "1")]
    consumers: usize,

    /// Buffer size
    #[arg(long, default_value = "1")]
    buffer_size: usize,
}
