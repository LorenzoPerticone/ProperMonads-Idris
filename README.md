# ProperMonads-Idris
Monad instances quite similar to the Haskell standard library, with a formal verification of all axioms.

IMPORTANT NOTICE: as of now the State and Continuation monad don't have a full implementation for *all* functor and monad axioms: this is due to the fact that I wasn't able to use some lemmas inside lambda abstraction. If anyone knows how to fix that, I'd be really happy to see *how*. This means that any commit/suggestion about that is very much welcome.
