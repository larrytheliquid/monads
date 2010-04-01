module Maybe where
open import Data.Nat
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

testShortCircuit : ( just 3 >> nothing >>= λ x → return (x * 4) ) ≡ nothing
testShortCircuit = refl

testChaining : ( just 3 >> just 4 >>= λ x → return (x * 4) ) ≡ just 16
testChaining = refl
