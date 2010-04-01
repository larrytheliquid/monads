module Monad where

record Monad (M : Set → Set) : Set where
  -- field
  --   return : (A : Set) → Monad M A

-- _>>_ : {A B : Set} → M A → M B → M B
-- x >> y = x >>= λ _ → y
