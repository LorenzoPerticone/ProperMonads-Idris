module MonadMaybe

import ProperMonad

%access public export
%default total

data PMaybe elem = PNothing | PJust elem

implementation PFunctor PMaybe where
  fmap f PNothing = PNothing
  fmap f (PJust x) = PJust (f x)

  functorial {fx = PNothing} = Refl
  functorial {fx = (PJust x)} = Refl

implementation PMonad PMaybe where
  unit x = PJust x
  unit_natural = Refl

  flatten PNothing = PNothing
  flatten (PJust x) = x
  flatten_natural {mmx = PNothing} = Refl
  flatten_natural {mmx = (PJust x)} = Refl

  monad_unital_l = Refl
  monad_unital_r {mx = PNothing} = Refl
  monad_unital_r {mx = (PJust x)} = Refl
  monad_associative {mmmx = PNothing} = Refl
  monad_associative {mmmx = (PJust x)} = Refl
