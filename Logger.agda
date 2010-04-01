module Logger where
open import Data.Unit
open import Data.Nat
open import Data.String hiding (_++_)
open import Data.List
open import Data.Product
open import Data.Function
open import Relation.Binary.PropositionalEquality

infixl 1 _>>=_ _>>_

Log = List String
data Logger (A : Set) : Set where
  logger : A → Log → Logger A

-- Controlled escape
runLogger : {A : Set} → Logger A → A × Log
runLogger (logger a j) = a , j

-- Special behavior
write : String → Logger ⊤
write s = logger tt [ s ]

return : {A : Set} → A → Logger A
return a = logger a []

_>>=_ : {A B : Set} → Logger A → (A → Logger B) → Logger B
m >>= f with runLogger m
... | a , j with runLogger (f a)
... | b , k = logger b (j ++ k)

_>>_ : {A B : Set} → Logger A → Logger B → Logger B
x >> y = x >>= λ _ → y

testBasic : (s₁ s₂ : String)(n : ℕ) →
  runLogger ( write s₁ >> write s₂ >> return n ) ≡ n , (s₁ ∷ s₂ ∷ [])
testBasic _ _ _ = refl

testWrite : (s : String) →
  runLogger ( write s >>= return ∘ id ) ≡ tt , [ s ]
testWrite _ = refl
