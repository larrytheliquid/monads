module List where
open import Data.Function
open import Relation.Binary.PropositionalEquality

infixl 1 _>>=_ _>>_
infixr 5 _∷_

data List (A : Set) : Set where
  [] : List A
  _∷_ : A → List A → List A

return : {A : Set} → A → List A
return a = a ∷ []

_>>=_ : {A B : Set} → List A → (A → List B) → List B
m >>= f = concat (map f m)
  where
    map : {A B : Set} → (A → B) → List A → List B
    map _ [] = []
    map f (x ∷ xs) = f x ∷ map f xs

    append : {A : Set} → List A →  List A → List A
    append [] ys = ys
    append (x ∷ xs) ys = x ∷ append xs ys

    concat : {A : Set} → List (List A) → List A
    concat [] = []
    concat (xs ∷ xss) = append xs (concat xss)

_>>_ : {A B : Set} → List A → List B → List B
x >> y = x >>= λ _ → y

private
  data _×_ (A B : Set) : Set where
    _,_ : (x : A) (y : B) → A × B

testComprehension : {A B : Set}(a b c : A)(x y z : B) →
  ( a ∷ b ∷ c ∷ [] >>= λ
    j → x ∷ y ∷ z ∷ [] >>= λ
    k → return (a , x) >> 
    return (j , k) )
  ≡ 
  ( (a , x) ∷ (a , y) ∷ (a , z) ∷ 
    (b , x) ∷ (b , y) ∷ (b , z) ∷
    (c , x) ∷ (c , y) ∷ (c , z) ∷ [] )
testComprehension _ _ _ _ _ _ = refl

testShortCircuit : {A B : Set}(a b c : A)(x y z : B) →
  ( a ∷ b ∷ c ∷ [] >>= λ
    j → x ∷ y ∷ z ∷ [] >>= λ
    k → _>>_ {A} {A × B} [] $
    return (j , k) )
  ≡ 
  []
testShortCircuit _ _ _ _ _ _ = refl
