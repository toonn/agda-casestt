module Okasaki where

open import Data.Bool using (Bool; true; false) renaming (T to So; not to ¬)

open import Data.Nat hiding (_<_; _≤_; _≟_; compare)
  renaming (decTotalOrder to ℕ-DTO)

open import Relation.Binary hiding (_⇒_)

module RBTree {a ℓ}(order : StrictTotalOrder a ℓ ℓ) where

  open module sto = StrictTotalOrder order
  A = Carrier
  
  pattern LT = tri< _ _ _
  pattern EQ = tri≈ _ _ _
  pattern GT = tri> _ _ _
  _≤_ = compare

  
  data Color : Set where
    R B : Color
  
  _=ᶜ_ : Color → Color → Bool
  R =ᶜ R = true
  B =ᶜ B = true
  _ =ᶜ _ = false

  Height = ℕ

  data Tree : Set a where
    E : Tree
    T : Color → Tree → A → Tree → Tree

  
  set = Tree

  empty : set
  empty = E

  member : A → set → Bool
  member x E = false
  member x (T _ a y b) with x ≤ y
  ... | LT = member x a
  ... | EQ = true
  ... | GT = member x b

  insert : A → set → set
  insert x s = makeBlack (ins s)
    where 
      balance : Color → set → A → set → set
      balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
      balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
      balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
      balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
      balance color a x b = T color a x b

      ins : set → set
      ins E = T R E x E
      ins (T color a y b) with x ≤ y
      ... | LT = balance color (ins a) y b
      ... | EQ = T color a y b
      ... | GT = balance color a y (ins b)

      makeBlack : set → set
      makeBlack E = E
      makeBlack (T _ a y b) = T B a y b
