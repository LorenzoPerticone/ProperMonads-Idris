module MonadState

import ProperMonad

%access public export
%default total

data PState s_ty v_ty = State (s_ty -> (s_ty, v_ty))

runState : PState s_ty v_ty -> s_ty -> (s_ty, v_ty)
runState (State f) state = f state

eval : (a, a -> b) -> b
eval (x, f) = f x

infixl 6 <**>
(<**>) : (a -> a') -> (b -> b') -> (a, b) -> (a', b')
(<**>) f g (x, x') = (f x, g x')

implementation PFunctor (PState s_ty) where
  fmap f (State g) = State $ (id <**> f) . g
-- this got very nasty very quickly, and it relies on eta equivalence inside constructors
  functorial {phi} {psi} {fx = State f} = ?functorial_rhs

implementation PMonad (PState s_ty) where
  unit x = State $ \s => (s, x)
  unit_natural {f} {x} = Refl

  flatten (State fm) = State $ \state => eval . (id <**> runState) $ fm state
-- same problem as in `functorial`
  flatten_natural {f} {mmx = State fm}= ?flatten_natural_rhs

  monad_unital_l {mx = State f} = rewrite (eta_equiv {f}) in Refl
-- same problem as in `functorial`
  monad_unital_r {mx = State f} = ?monad_unital_r_rhs
-- same problem as in `functorial`
  monad_associative {mmmx = State fmm} = ?monad_associative_rhs
