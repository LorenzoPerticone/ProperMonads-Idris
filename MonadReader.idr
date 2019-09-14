module MonadReader

import ProperMonad

%access public export
%default total

data PReader in_ty out_ty = Reader (in_ty -> out_ty)

runReader : PReader in_ty out_ty -> in_ty -> out_ty
runReader (Reader f) = f

implementation PFunctor (PReader in_ty) where
  fmap f mg = Reader $ f . runReader mg
  functorial {phi} {psi} {fx = Reader f} = Refl

implementation PMonad (PReader in_ty) where
  unit x = Reader (\_ => x)
  unit_natural = Refl

  flatten mf = Reader $ \x => runReader (runReader mf x) x
  flatten_natural {f} {mmx = Reader mg}= Refl

  monad_unital_l {mx = Reader (f)} = Refl
  monad_unital_r {mx = Reader (f)} = Refl
  monad_associative {mmmx = Reader fmm} = Refl
