module MonadEither

import ProperMonad

%access public export
%default total

data PEither error elem = PLeft error | PRight elem

fmap_peither : (a -> b) -> PEither t a -> PEither t b
fmap_peither f (PLeft x) = PLeft x
fmap_peither f (PRight x) = PRight (f x)

implementation PFunctor (PEither error) where
  fmap = fmap_peither
  functorial {fx = (PLeft l)} = Refl
  functorial {fx = (PRight r)} = Refl

implementation PMonad (PEither t) where
  unit x = PRight x
  unit_natural = Refl

  flatten (PLeft l) = PLeft l
  flatten (PRight r) = r
  flatten_natural {mmx = (PLeft l)} = Refl
  flatten_natural {mmx = (PRight r)} = Refl

  monad_unital_l = Refl
  monad_unital_r {mx = (PLeft l)} = Refl
  monad_unital_r {mx = (PRight r)} = Refl
  monad_associative {mmmx = (PLeft l)} = Refl
  monad_associative {mmmx = (PRight r)} = Refl
