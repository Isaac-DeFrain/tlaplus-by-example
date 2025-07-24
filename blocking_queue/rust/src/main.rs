//! Main entry point

use clap::Parser;
use std::{
    error::Error,
    sync::{Arc, Condvar, Mutex},
    thread,
};

mod cli;

struct Queue {
    queue: Mutex<Vec<usize>>,
    consumer_cond_var: Condvar,
    producer_cond_var: Condvar,
}

fn main() -> Result<(), Box<dyn Error>> {
    // Parse command line arguments
    let cli = cli::Cli::try_parse()?;
    let num_producers = cli.producers;
    let num_consumers = cli.consumers;
    let buffer_size = cli.buffer_size;

    // Initialize empty buffer
    let queue = Queue {
        queue: Mutex::new(Vec::with_capacity(buffer_size)),
        consumer_cond_var: Condvar::new(),
        producer_cond_var: Condvar::new(),
    };
    let buffer = Arc::new(queue);

    println!(
        "Buffer size = {}, # Producers = {}, # Consumers: {}",
        buffer_size, num_producers, num_consumers
    );

    let producers = (0..num_producers)
        .map(|id| {
            let buffer = Arc::clone(&buffer);
            thread::spawn(move || {
                loop {
                    let Queue {
                        queue,
                        consumer_cond_var,
                        producer_cond_var,
                    } = &*buffer;
                    let mut buffer = queue.lock().unwrap();

                    // Wait until there is space in the buffer
                    while buffer.len() == buffer_size {
                        println!("Producer {} - waiting on full buffer", id);
                        buffer = producer_cond_var.wait(buffer).unwrap();
                    }

                    // Push data to the end of the buffer & notify a waiting consumer
                    buffer.push(id);
                    consumer_cond_var.notify_one();
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
                    let Queue {
                        queue,
                        consumer_cond_var,
                        producer_cond_var,
                    } = &*buffer;
                    let mut buffer = queue.lock().unwrap();

                    // Wait until there is an item in the buffer
                    while buffer.is_empty() {
                        println!("Consumer {} - waiting on empty buffer", id);
                        buffer = consumer_cond_var.wait(buffer).unwrap();
                    }

                    // Consume first item from the buffer & notify a waiting producer
                    let item = buffer.remove(0);
                    producer_cond_var.notify_one();
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
