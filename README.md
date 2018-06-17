# Idris-chain 
Dependently typed blockchain experiments in Idris.

 * `Blockchain` module implements a blockchain (cryptographic linked list) with
type guarantee that hashes are correct and the chain is not compromised.

_Proof of type?_ :)

__Work-in-progress__

Idris instructions
------------------
I am using _idris 1.2_
This project includes make file with configuration to build and run tests.
To use interactive repl:
```
> cd src 
> idris repl --package contrib
```
