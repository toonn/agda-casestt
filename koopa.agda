{-

    Verified Koopa Troopa Movement
             Toon Nolten

-}

module koopa where
  open import Data.Nat
  open import Data.Fin renaming (_+_ to _F+_; _<_ to _F<_; suc to fsuc;
    zero to fzero)
  open import Data.Vec renaming (map to vmap; lookup to vlookup;
                                     replicate to vreplicate)
  open import Data.Unit
  open import Data.Empty

  module Matrix where
    data Matrix (A : Set) : ℕ → ℕ → Set where
      Mat : {w h : ℕ} → Vec (Vec A w) h → Matrix A w h

    lookup : ∀ {w h} {A : Set} → Fin h → Fin w → Matrix A w h → A
    lookup row column (Mat rows) = vlookup column (vlookup row rows)
  open Matrix

  data Color : Set where
    Green : Color
    Red : Color

  data KoopaTroopa : Color → Set where
    _KT : (c : Color) → KoopaTroopa c

  data Material : Set where
    gas    : Material
    -- liquid : Material
    solid  : Material

  data Clearance : Set where
    Low  : Clearance
    High : Clearance
    God  : Clearance

  record Position : Set where
    constructor pos
    field
      x   : ℕ
      y   : ℕ
      mat : Material
      clr : Clearance

  data _c>_ : Color → Clearance → Set where
    <red>   : ∀ {c} → c c> Low
    <green> : Green c> High

  data _follows_⟨_⟩ : Position → Position → Color → Set where
    stay  : ∀ {c x y} → pos x y gas Low follows pos x y gas Low ⟨ c ⟩
    next  : ∀ {c cl x y}{{_ : c c> cl}} →
            pos (suc x) y gas cl follows pos x y gas Low ⟨ c ⟩
    back  : ∀ {c cl x y}{{_ : c c> cl}} →
            pos x y gas cl follows pos (suc x) y gas Low ⟨ c ⟩
    -- jump  : ∀ {c x y} → pos x (suc y) gas High follows pos x y gas Low ⟨ c ⟩
    fall  : ∀ {c cl x y} → pos x y gas cl follows pos x (suc y) gas High ⟨ c ⟩


  infixr 5 _↠⟨_⟩_
  data Path {c : Color} (Koopa : KoopaTroopa c) :
       Position → Position → Set where
    []  : ∀ {p} → Path Koopa p p
    _↠⟨_⟩_ : {q r : Position} → (p : Position) → q follows p ⟨ c ⟩
                → (qs : Path Koopa q r) → Path Koopa p r

  ex_path : Path (Red KT) (pos 0 0 gas Low) (pos 0 0 gas Low)
  ex_path = pos 0 0 gas Low ↠⟨ next ⟩
            pos 1 0 gas Low ↠⟨ back ⟩
            pos 0 0 gas Low ↠⟨ stay ⟩ []

  matToPosVec : {n : ℕ} → Vec Material n → Vec Material n → ℕ → ℕ →
                   Vec Position n
  matToPosVec []           []        _ _ = []
  matToPosVec (mat ∷ mats) (under ∷ unders) x y =
    pos x y mat cl ∷ matToPosVec mats unders (x + 1) y
      where
        clearance : Material → Material → Clearance
        clearance gas   gas   = High
        clearance gas   solid = Low
        clearance solid _     = God
        cl = clearance mat under

  matToPosVecs : {w h : ℕ} → Vec (Vec Material w) h → Vec (Vec Position w) h
  matToPosVecs [] = []
  matToPosVecs (_∷_ {y} mats matss) =
    matToPosVec mats (unders matss gas) 0 y ∷ matToPosVecs matss
    where
      unders : ∀ {m n ℓ}{A : Set ℓ} → Vec (Vec A m) n → A → Vec A m
      unders [] fallback = vreplicate fallback
      unders (us ∷ _) _ = us

  matsToMat : {w h : ℕ} → Vec (Vec Material w) h → Matrix Position w h
  matsToMat matss = Mat (reverse (matToPosVecs matss))

  □ : Material
  □ = gas
  ■ : Material
  ■ = solid
  example_level : Matrix Position 10 7
  example_level = matsToMat (
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (□ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ []) ∷ 
    (■ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ □ ∷ ■ ∷ []) ∷ 
    (■ ∷ ■ ∷ ■ ∷ ■ ∷ ■ ∷ □ ∷ □ ∷ ■ ∷ ■ ∷ ■ ∷ []) ∷ [])

  _<'_ : ℕ → ℕ → Set
  m <' zero = ⊥
  zero <' suc n = ⊤
  suc m <' suc n = m <' n

  fromNat : ∀ {n}(k : ℕ){_ : k <' n} → Fin n
  fromNat {zero} k {}
  fromNat {suc n} zero = fzero
  fromNat {suc n} (suc k) {p} = fsuc (fromNat k {p})
 
  f : ∀ {n}(k : ℕ){_ : k <' n} → Fin n
  f = fromNat

  p : (x : Fin 10) → (y : Fin 7) → Position
  p x y = lookup y x example_level

  red_path_one : Path (Red KT) (p (f 7) (f 6)) (p (f 8) (f 6))
  red_path_one = p (f 7) (f 6) ↠⟨ back ⟩
                 p (f 6) (f 6) ↠⟨ next ⟩
                 p (f 7) (f 6) ↠⟨ next ⟩
                 p (f 8) (f 6) ↠⟨ stay ⟩ []

  red_path_two : Path (Red KT) (p (f 2) (f 1)) (p (f 3) (f 1))
  red_path_two = p (f 2) (f 1) ↠⟨ back ⟩
                 p (f 1) (f 1) ↠⟨ next ⟩
                 p (f 2) (f 1) ↠⟨ next ⟩
                 p (f 3) (f 1) ↠⟨ next ⟩
                 p (f 4) (f 1) ↠⟨ back ⟩
                 p (f 3) (f 1) ↠⟨ stay ⟩
                 []

  -- -- Type error shows up 'late' because 'cons' is right associative
  -- red_nopath_one : Path (Red KT) (p (f 1) (f 1)) (p (f 0) (f 1))
  -- red_nopath_one = p (f 1) (f 1) ↠⟨ back ⟩
  --                  p (f 0) (f 1) ↠⟨ stay ⟩
  --                  []

  -- -- Red KoopaTroopa can't step into a wall
  -- red_nopath_two : Path (Red KT) (p (f 1) (f 1)) (p (f 0) (f 1))
  -- red_nopath_two = p (f 1) (f 1) ↠⟨ back ⟩ []

  -- -- Red KoopaTroopa can't step into air
  -- red_nopath_three : Path (Red KT) (p (f 4) (f 1)) (p (f 5) (f 1))
  -- red_nopath_three = p (f 4) (f 1) ↠⟨ next ⟩ []

  -- Any path that is valid for red KoopaTroopas, is also valid for green
  -- KoopaTroopas because we did not constrain KoopaTroopas to only turn
  -- When there is an obstacle
  green_path_one : Path (Green KT) (p (f 7) (f 6)) (p (f 8) (f 6))
  green_path_one = p (f 7) (f 6) ↠⟨ back ⟩
                   p (f 6) (f 6) ↠⟨ next ⟩
                   p (f 7) (f 6) ↠⟨ next ⟩
                   p (f 8) (f 6) ↠⟨ stay ⟩ []

  green_path_two : Path (Green KT) (p (f 7) (f 6)) (p (f 5) (f 0))
  green_path_two = p (f 7) (f 6) ↠⟨ back ⟩
                   p (f 6) (f 6) ↠⟨ back ⟩
                   p (f 5) (f 6) ↠⟨ fall ⟩
                   p (f 5) (f 5) ↠⟨ fall ⟩
                   p (f 5) (f 4) ↠⟨ back ⟩
                   p (f 4) (f 4) ↠⟨ back ⟩
                   p (f 3) (f 4) ↠⟨ back ⟩
                   p (f 2) (f 4) ↠⟨ fall ⟩
                   p (f 2) (f 3) ↠⟨ fall ⟩
                   p (f 2) (f 2) ↠⟨ fall ⟩
                   p (f 2) (f 1) ↠⟨ back ⟩
                   p (f 1) (f 1) ↠⟨ next ⟩
                   p (f 2) (f 1) ↠⟨ next ⟩
                   p (f 3) (f 1) ↠⟨ next ⟩
                   p (f 4) (f 1) ↠⟨ next ⟩
                   p (f 5) (f 1) ↠⟨ fall ⟩
                   []

  -- -- Green KoopaTroopa can't step into a wall
  -- green_nopath_one : Path (Green KT) (p (f 1) (f 1)) (p (f 0) (f 1))
  -- green_nopath_one = p (f 1) (f 1) ↠⟨ back ⟩ []
