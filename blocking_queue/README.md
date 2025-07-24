# TLA+ by Example - Blocking Queue

TLA+ is a formal specification language used for designing, modeling, and verifying complex systems. It allows developers to specify the behavior of systems in a mathematical way, which can help in identifying potential issues before implementation.

- Math > Programming: higher level of abstraction makes it easier to reason about systems
- Easiest to learn through example

Based on this [Linux Foundation talk](https://www.youtube.com/watch?v=H6PjGdd6vGg)

All code available on my [github](https://github.com/Isaac-DeFrain/tlaplus-by-example/tree/main/blocking_queue)

## Blocking Queue

### Why?

- Blocking queues are a common concurrency pattern
- Concurrent and distributed systems are hard to reason about
- It is very difficult to _prove_ code is deadlock-free
- TLA+ provides a way to specify, verify, and prove the behavior of such systems

### What?

- `m` producers
- `n` consumers
- blocking, shared queue of fixed size `l`
- no deadlocks

### How?

- producers
  - put item in the queue
  - wait if full
- consumers
  - take item from the queue
  - wait if empty
- a waiting/blocked thread is notified when an item is added or removed
  - producers notify waiting consumers
  - consumers notify waiting producers

How can we prove that our program is deadlock free?

## Project Structure

- [rust impl](./rust/)
- [tla+ spec](./tla/)

### Run the example rust impl

Go to the `rust` directory and do

```zsh
cargo run -- --producers 2 --consumers 1 --buffer-size 1
```

### Model check the TLA+ spec

Use the TLA+ extension, open the [spec](./tla/blocking_queue.tla) or [config](./tla/blocking_queue.cfg), and run TLC from the command pallete
