module MonadList

import ProperMonad

%access public export
%default total

data PList elem = PNil | PCons elem (PList elem)

concat_plist : PList elem -> PList elem -> PList elem
concat_plist PNil ys = ys
concat_plist (PCons x xs) ys = PCons x (concat_plist xs ys)

fmap_plist : (elem1 -> elem2) -> PList elem1 -> PList elem2
fmap_plist f PNil = PNil
fmap_plist f (PCons x xs) = PCons (f x) (fmap_plist f xs)

fmap_plist_morphism : {f : elem1 -> elem2} ->
                      {xs : PList elem1} ->
                      {ys : PList elem1} ->
                      concat_plist (fmap_plist f xs) (fmap_plist f ys) =
                      fmap_plist f (concat_plist xs ys)
fmap_plist_morphism {xs = PNil} = Refl
fmap_plist_morphism {f} {xs = (PCons x xs')} {ys} =
  let indHyp = fmap_plist_morphism {f} {xs = xs'} {ys}
  in rewrite indHyp in Refl

concat_plist_pnil : {xs : PList elem} ->
                    concat_plist xs PNil = xs
concat_plist_pnil {xs = PNil} = Refl
concat_plist_pnil {xs = (PCons x xs')} =
  let indHyp = concat_plist_pnil {xs = xs'}
  in rewrite indHyp in Refl

concat_plist_associative : {xs : PList elem} ->
                           {ys : PList elem} ->
                           {zs : PList elem} ->
                           concat_plist xs (concat_plist ys zs) = concat_plist (concat_plist xs ys) zs
concat_plist_associative {xs = PNil} {ys = PNil} = Refl
concat_plist_associative {xs = PNil} {ys = (PCons y ys')} = Refl
concat_plist_associative {xs = (PCons x xs')} {ys = PNil} =
  let hyp = concat_plist_pnil {xs = xs'}
  in rewrite hyp in Refl
concat_plist_associative {xs = (PCons x xs')} {ys} {zs} =
  let indHyp = concat_plist_associative {xs = xs'} {ys} {zs}
  in rewrite indHyp in Refl

flatten_plist : PList (PList elem) -> PList elem
flatten_plist PNil = PNil
flatten_plist (PCons xs xss) = concat_plist xs (flatten_plist xss)

flatten_concat_plist : {xss : PList (PList elem)} ->
                      {yss : PList (PList elem)} ->
                      flatten_plist (concat_plist xss yss) = concat_plist (flatten_plist xss) (flatten_plist yss)
flatten_concat_plist {xss = PNil} = Refl
flatten_concat_plist {xss = (PCons xs xss')} {yss = yss} =
  let indHyp = flatten_concat_plist {xss = xss'} {yss}
      otherHyp = concat_plist_associative {xs = xs} {ys = flatten_plist xss'} {zs = flatten_plist yss}
  in rewrite indHyp in rewrite otherHyp in Refl

implementation PFunctor PList where
  fmap = fmap_plist
  functorial {fx = PNil} = Refl
  functorial {phi} {psi} {fx = (PCons x xs)} =
    let indHyp = functorial {phi} {psi} {fx = xs}
    in rewrite indHyp in Refl

implementation PMonad PList where
  unit = \x => PCons x PNil
  unit_natural = Refl

  flatten = flatten_plist
  flatten_natural {mmx = PNil} = Refl
  flatten_natural {f} {mmx = (PCons xs xss)} =
    let indHyp = flatten_natural {f} {mmx = xss}
        otherHyp = fmap_plist_morphism {f} {xs} {ys = flatten xss}
    in rewrite indHyp in rewrite otherHyp in Refl

  monad_unital_l {mx} = concat_plist_pnil {xs = mx}
  monad_unital_r {mx = PNil} = Refl
  monad_unital_r {mx = (PCons x xs)} =
    let indHyp = monad_unital_r {mx = xs}
    in rewrite indHyp in Refl
  monad_associative {mmmx = PNil} = Refl
  monad_associative {mmmx = (PCons xss xsss)} =
    let indHyp = monad_associative {mmmx = xsss}
        otherHyp = flatten_concat_plist {xss = xss} {yss = flatten xsss}
    in rewrite otherHyp in rewrite indHyp in Refl
