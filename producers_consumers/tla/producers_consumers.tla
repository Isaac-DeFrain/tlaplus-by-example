----- MODULE producers_consumers -----

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Producers,  (* nonempty set of producers *)
    Consumers,  (* nonempty set of consumers *)
    BufCapacity (* maximum number of items in buffer *)

\* Assumptions enforced in the initial state

ASSUME Assumption ==
    /\ Producers # {}                (* at least one producer *)
    /\ Consumers # {}                (* at least one consumer *)
    /\ Producers \cap Consumers = {} (* no thread is both consumer and producer *)
    /\ BufCapacity \in (Nat \ {0})   (* buffer capacity is at least 1 *)

\* Variables defining the state of the system

VARIABLES
    buffer, (* sequence of items in buffer *)
    waitSet (* set of waiting threads *)

vars == <<buffer, waitSet>>

-------------------------------------

\* Helpers

\* Notify a waiting thread to wake up
Notify ==
    IF waitSet # {}
    THEN \E t \in waitSet: waitSet' = waitSet \ {t}
    ELSE UNCHANGED waitSet

\* Thread waits to be notified
Wait(t) ==
    /\ waitSet' = waitSet \cup {t}
    /\ UNCHANGED buffer

-------------------------------------

\* Actions

\* Active producer puts an item in the buffer or waits
Produce(p) ==
    /\ p \notin waitSet
    /\ \/ /\ Len(buffer) < BufCapacity
          /\ buffer' = Append(buffer, p)
          /\ Notify
       \/ /\ Len(buffer) = BufCapacity
          /\ Wait(p)

\* Active consumer takes an item from the buffer or waits
Consume(c) ==
    /\ c \notin waitSet
    /\ \/ /\ buffer # <<>>
          /\ buffer' = Tail(buffer)
          /\ Notify
       \/ /\ buffer = <<>>
          /\ Wait(c)

-------------------------------------

\* Specification

\* Initial state
\* - empty buffer
\* - no waiting threads
Init ==
    /\ buffer = <<>>
    /\ waitSet = {}

\* Next action
\* either:
\* - an active producer produces
\* - an active consumer consumes
Production == \E p \in Producers \ waitSet: Produce(p)
Consumption == \E c \in Consumers \ waitSet: Consume(c)
Next == Production \/ Consumption

Spec ==
    /\ Init
    /\ [][Next]_vars

=====================================
