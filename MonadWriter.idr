module MonadWriter

import ProperMonad

%access public export
%default total

data PWriter log_ty elem = Write (log_ty, elem)

implementation PFunctor (PWriter log_ty) where
  fmap f (Write (log, x)) = Write (log, f x)
  functorial {fx = (Write (a, b))} = Refl

implementation PMonoid log_ty => PMonad (PWriter log_ty) where
  unit x = Write (zero, x)
  unit_natural = Refl

  flatten (Write (a1, Write (a2, b))) = Write (a1 <++> a2, b)
  flatten_natural {mmx = (Write (a1, Write (a2, b)))} = Refl

  monad_unital_l {mx = (Write (a, b))} =
    let otherHyp = unital_l {x = a}
    in rewrite otherHyp in Refl
  monad_unital_r {mx = (Write (a, b))} =
    let otherHyp = unital_r {x = a}
    in rewrite otherHyp in Refl
  monad_associative {mmmx = (Write (a1, Write (a2, Write (a3, x))))} =
    let otherHyp = associative {x = a1} {y = a2} {z = a3}
    in rewrite otherHyp in Refl
