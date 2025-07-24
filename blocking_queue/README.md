# TLA+ by Example

TLA+ is a formal specification language used for designing, modeling, and verifying complex systems. It allows developers to specify the behavior of systems in a mathematical way, which can help in identifying potential issues before implementation.

- Math > Programming: higher level of abstraction makes it easier to reason about systems
- Easiest to learn through example

Based on this [Linux Foundation talk](https://www.youtube.com/watch?v=H6PjGdd6vGg)

## Install TLA+ Toolbox

- install `java`

    ```zsh
    brew install java
    ```

    symlink it

    ```zsh
    sudo ln -sfn /opt/homebrew/opt/openjdk/libexec/openjdk.jdk \
        /Library/Java/JavaVirtualMachines/openjdk.jdk
    ```

    and check

    ```zsh
    $ java -version
    openjdk version "24.0.1" 2025-04-15
    OpenJDK Runtime Environment Homebrew (build 24.0.1)
    OpenJDK 64-Bit Server VM Homebrew (build 24.0.1, mixed mode, sharing)
    ```

- insall TLA+ toolbox

    ```zsh
    brew install tla+-toolbox
    ```

- [latest release](https://github.com/tlaplus/tlaplus/releases/latest)

- install [vscode/cursor extension](https://github.com/tlaplus/vscode-tlaplus)

## TLA+ Example (Blocking Queue)

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
