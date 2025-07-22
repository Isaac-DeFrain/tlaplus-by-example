//! Main entry point

use clap::Parser;
use std::{
    error::Error,
    sync::{Arc, Condvar, Mutex},
    thread,
};

mod cli;

fn main() -> Result<(), Box<dyn Error>> {
    // Parse command line arguments
    let cli = cli::Cli::try_parse()?;
    let num_producers = cli.producers;
    let num_consumers = cli.consumers;
    let buffer_size = cli.buffer_size;

    // Initialize empty buffer
    let queue = <Vec<usize>>::with_capacity(buffer_size);
    let buffer = Arc::new((Mutex::new(queue), Condvar::new()));

    println!(
        "Buffer size = {}, # Producers = {}, # Consumers: {}",
        buffer_size, num_producers, num_consumers
    );

    let producers = (0..num_producers)
        .map(|id| {
            let buffer = Arc::clone(&buffer);
            thread::spawn(move || {
                loop {
                    let (lock, cond_var) = &*buffer;
                    let mut buffer = lock.lock().unwrap();

                    // Wait until there is space in the buffer
                    while buffer.len() == buffer_size {
                        println!("Producer {} - waiting on full buffer", id);
                        buffer = cond_var.wait(buffer).unwrap();
                    }

                    // Push data to the end of the buffer
                    buffer.push(id);
                    cond_var.notify_all();
                    println!("Producer {} - produced item", id);
                }
            })
        })
        .collect::<Vec<_>>();

    let consumers = (0..num_consumers)
        .map(|id| {
            let buffer = Arc::clone(&buffer);
            thread::spawn(move || {
                loop {
                    let (lock, cond_var) = &*buffer;
                    let mut buffer = lock.lock().unwrap();

                    // Wait until there is an item in the buffer
                    while buffer.is_empty() {
                        println!("Consumer {} - waiting on empty buffer", id);
                        buffer = cond_var.wait(buffer).unwrap();
                    }

                    // Consume first item from the buffer
                    let item = buffer.remove(0);
                    cond_var.notify_all();
                    println!("Consumer {} - consumed item {}", id, item);
                }
            })
        })
        .collect::<Vec<_>>();

    for producer in producers {
        producer.join().expect("Producer thread should succeed");
    }

    for consumer in consumers {
        consumer.join().expect("Consumer thread should succeed");
    }

    Ok(())
}
