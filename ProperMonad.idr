module ProperMonad

%access public export
%default total

eta_equiv : {a : Type} -> {b : Type} -> {f : a -> b} -> f = (\x : a => f x)
eta_equiv {f} = Refl

extensionality : {f : a -> b} -> {g : a -> b} ->
                 (eql : (x : a) -> f x = g x) -> f = g
extensionality {f} {g} {eql} = believe_me (f, eql, g)

appl_equality : {f : a -> b} -> {g : a -> b} ->
                (f = g) -> (x : a) -> (f x = g x)
appl_equality {f} {g} eql x = rewrite eql in Refl

infixl 6 <++>

interface PSemigroup s where
  (<++>) : s -> s -> s
  associative : {x : s} -> {y : s} -> {z : s} ->
                x <++> (y <++> z) = (x <++> y) <++> z

interface PSemigroup m => PMonoid m where
  zero : m
  unital_l : {x : m} -> zero <++> x = x
  unital_r : {x : m} -> x <++> zero = x

interface PFunctor (f : Type -> Type) where
  fmap : (a -> b) -> f a -> f b
  functorial : {phi : b -> c} -> {psi : a -> b} -> {fx : f a} ->
               fmap (phi . psi) fx = (fmap phi . fmap psi) fx

interface PFunctor m => PMonad (m : Type -> Type) where
  unit : a -> m a
  unit_natural : {f : a -> b} -> {x : a} ->
                 (unit . f) x = (fmap f . unit) x

  flatten : m (m a) -> m a
  flatten_natural : {f : a -> b} -> {mmx : m (m a)} ->
                   (flatten . fmap (fmap f)) mmx = (fmap f . flatten) mmx

  monad_unital_l : {mx : m a} ->
                   (flatten . unit) mx = mx
  monad_unital_r : {mx : m a} ->
                   (flatten . fmap unit) mx = mx
  monad_associative : {mmmx : m (m (m a))} ->
                      (flatten . flatten) mmmx = (flatten . fmap flatten) mmmx
