module MonadCont

import ProperMonad

%access public export
%default total

data PCont result argument = Cont ((argument -> result) -> result)

runCont : PCont result argument -> (argument -> result) -> result
runCont (Cont f) = f

implementation PFunctor (PCont result) where
  fmap f mg = Cont $ \h => runCont mg (h . f)
  functorial {phi} {psi} {fx = Cont f} = Refl

lemma_unital : {a : Type} -> {b : Type} ->
               {f : (a -> b) -> b} ->
               (\g => f (\x => g x)) = (\g => f g)
lemma_unital {a} {b} {f} =
  extensionality {f = \g => f g} {g = \g => f (\x => g x)} (\_ => Refl)

implementation PMonad (PCont result) where
  unit x = Cont $ \f => f x
  unit_natural {f} {x} = Refl

  flatten (Cont fm) = Cont $ \f => fm (\mx => runCont mx f)
  flatten_natural {f} {mmx = Cont fm} = Refl

  monad_unital_l {mx = Cont f} = Refl
  monad_unital_r {mx = Cont f} =
    let hyp = lemma_unital {f}
    in rewrite hyp in Refl

-- here I just gave up (twice)
  monad_associative {mmmx = Cont fmm} =
    let hyp = lemma2 in ?monad_associative_rhs
    where lemma1 : {a : Type} -> {b : Type} ->
                   {mmf : PCont a (PCont a b)} ->
                   {f : b -> a} ->
                   runCont mmf (\mg => runCont mg f) = runCont (flatten mmf) f
          lemma1 {mmf = Cont fm} = Refl
          lemma2 : {a : Type} -> {b : Type} ->
                   {f : b -> a} ->
                   {fmm : (PCont a (PCont a b) -> a) -> a} ->
                   fmm (\mmf => runCont mmf (\mg => runCont mg f)) =
                   fmm (\mmf => runCont (flatten mmf) f)
          lemma2 {a} {b} {f} = --?lemma2_rhs
            let hyp = \mmf => lemma1 {a} {b} {f} {mmf}
            in ?lemma2_rhs
