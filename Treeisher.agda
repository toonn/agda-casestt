{-
  Verified Red-Black Trees
        Toon Nolten

  Based on Chris Okasaki's "Red-Black Trees in a Functional Setting"
  where he uses red-black trees to implement sets.

  Invariants
  ----------

  1. No red node has a red parent
  2. Every Path from the root to an empty node contains the same number of
     black nodes.
    (Empty nodes are considered black)
-}
module Treeisher where

open import Data.Bool using (Bool; true; false) renaming (T to So; not to ¬)
_⇒_ : ∀{ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
P ⇒ T = {{p : P}} → T
infixr 3 _⇒_

if_then_else_ : ∀{ℓ}{A : Set ℓ} b → (So b ⇒ A) → (So (¬ b) ⇒ A) → A
if true  then t else f = t
if false then t else f = f

open import Data.Nat hiding (_<_; _≤_; _≟_; compare)
  renaming (decTotalOrder to ℕ-DTO)
open import Level hiding (suc)
open import Relation.Binary hiding (_⇒_)

open import Data.Sum using (_⊎_) renaming (inj₁ to h+0; inj₂ to h+1)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)

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

  data Tree : Color → Height → Set a where
    E : Tree B 0
    R : ∀{h} → Tree B h → A → Tree B h → Tree R h
    B : ∀{cl cr h} → Tree cl h → A → Tree cr h → Tree B (suc h)

  data IRTree : Height → Set a where
    IRl : ∀{h} → Tree R h → A → Tree B h → IRTree h
    IRr : ∀{h} → Tree B h → A → Tree R h → IRTree h

  data OutOfBalance : Height → Set a where
    _◂_◂_ : ∀{c h} → IRTree h → A → Tree c h → OutOfBalance h
    _▸_▸_ : ∀{c h} → Tree c h → A → IRTree h → OutOfBalance h

  data Treeish : Color → Height → Set a where
    RB : ∀{c h} → Tree c h → Treeish c h
    IR : ∀{h} → IRTree h → Treeish R h

  -- Insertion

  balance : ∀{h} → OutOfBalance h → Treeish R (suc h)
  balance (IRl (R a x b) y c ◂ z ◂ d) = RB (R (B a x b) y (B c z d))
  balance (IRr a x (R b y c) ◂ z ◂ d) = RB (R (B a x b) y (B c z d))
  balance (a ▸ x ▸ IRl (R b y c) z d) = RB (R (B a x b) y (B c z d))
  balance (a ▸ x ▸ IRr b y (R c z d)) = RB (R (B a x b) y (B c z d))

  blacken : ∀{c h} → (Treeish c h)
            → (if c =ᶜ B then Tree B h else Tree B (suc h))
  blacken (RB E) = E
  blacken (RB (R l b r)) = (B l b r)
  blacken (RB (B l b r)) = (B l b r)
  blacken (IR (IRl l b r)) = (B l b r)
  blacken (IR (IRr l b r)) = (B l b r)

  -- ins as in haskell, cases with a hole are impossible
  -- (look at the original type for ins to be convinced)
  -- But how do we convince agda of this?
  -- Absurd pattern doesn't help because agda can't rule out the constructors
  -- for IRTree.
  ins : ∀{c h} → (a : A) → (t : Tree c h)
        → Σ[ c' ∈ Color ] (Treeish c' h)
  ins a E = R , RB (R E a E)
  --
  ins a (R _ b _) with a ≤ b
  ins a (R l _ _) | LT with ins a l
  ins _ (R _ b r) | LT | R , RB t = R , IR (IRl t b r)
  ins _ (R _ b r) | LT | R , IR t = {!!}
  ins _ (R _ b r) | LT | B , RB t = R , (RB (R t b r))
  ins _ (R l b r) | EQ = R , RB (R l b r)
  ins a (R _ _ r) | GT with ins a r
  ins _ (R l b _) | GT | R , RB t = R , (IR (IRr l b t))
  ins _ (R l b _) | GT | R , IR t = {!!}
  ins _ (R l b _) | GT | B , RB t = R , (RB (R l b t))
  --
  ins a (B _ b _) with a ≤ b
  ins a (B l _ _) | LT with ins a l
  ins _ (B {R} _ b r) | LT | .R , IR t = R , balance (t ◂ b ◂ r)
  ins _ (B _ b r) | LT | c , RB t = B , RB (B t b r)
  ins _ (B {B} _ b r) | LT | .R , IR t = {!!}
  ins _ (B l b r) | EQ = B , RB (B l b r)
  ins a (B _ _ r) | GT with ins a r
  ins _ (B {cr = R} l b _) | GT | c , RB t = B , RB (B l b t)
  ins _ (B {cr = R} l b _) | GT | .R , IR t = R , balance (l ▸ b ▸ t)
  ins _ (B {cr = B} l b _) | GT | c , RB t = B , RB (B l b t)
  ins _ (B {cr = B} l b _) | GT | .R , IR t = {!!}

  insert : ∀{c h} → (a : A) → (t : Tree c h)
           → Tree B h ⊎ Tree B (suc h)
  insert a t with ins a t
  ... | R , t' = h+1 (blacken t')
  ... | B , t' = h+0 (blacken t')


  -- Simple Set Operations
  set : ∀{c h} → Set _
  set {c}{h} = Tree c h

  empty : set
  empty = E

  member : ∀{c h} → (a : A) → set {c}{h} → Bool
  member a E = false
  member a (R l b r) with a ≤ b
  ... | LT = member a l
  ... | EQ = true
  ... | GT = member a r
  member a (B l b r) with a ≤ b
  ... | LT = member a l
  ... | EQ = true
  ... | GT = member a r




-- Usage example

open import Relation.Binary.Properties.DecTotalOrder ℕ-DTO
ℕ-STO : StrictTotalOrder _ _ _
ℕ-STO = strictTotalOrder

open module rbtree = RBTree ℕ-STO

t0 : Tree B 2
t0 = B (R (B E 1 E) 2 (B (R E 3 E) 5 (R E 7 E)))
       8
       (B E 9 (R E 10 E))

t1 : Tree B 3
t1 = B (B (B E 1 E) 2 (B E 3 E))
       4
       (B (B E 5 (R E 7 E)) 8 (B E 9 (R E 10 E)))

t2 : Tree B 3
t2 = B (B (B E 1 E) 2 (B E 3 E))
       4
       (B (R (B E 5 E) 6 (B E 7 E)) 8 (B E 9 (R E 10 E)))

open import Relation.Binary.PropositionalEquality
t1≡t0+4 : h+1 t1 ≡ insert 4 t0
t1≡t0+4 = refl

t2≡t1+6 : h+0 t2 ≡ insert 6 t1
t2≡t1+6 = refl
