module Maybe where
open import Data.Function
open import Relation.Binary.PropositionalEquality

infixl 1 _>>=_ _>>_

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just : (x : A) → Maybe A

return : {A : Set} → A → Maybe A
return x = just x

_>>=_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
nothing >>= _ = nothing
just v >>= f = f v

_>>_ : {A B : Set} → Maybe A → Maybe B → Maybe B
x >> y = x >>= λ _ → y

testShortCircuit : {A B : Set}(a : A) →
  ( just a >> nothing {B} >>= return ∘ id ) ≡ nothing
testShortCircuit _ = refl

testChaining : {A B : Set}(a : A)(b : B) →
  ( just a >> just b >>= return ∘ id ) ≡ just b
testChaining _ _ = refl
