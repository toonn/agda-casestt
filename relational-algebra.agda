{-

    Practical Relational Algebra
            Toon Nolten
              based on
          The Power Of Pi

-}
module relational-algebra where

open import Data.Empty
open import Data.Unit hiding (_≤_)
open import Data.Bool
open import Data.Nat
open import Data.Integer hiding (show)
open import Data.List
open import Data.Char hiding (_==_) renaming (show to charToString)
open import Data.Vec hiding (_++_; lookup; map; foldr; _>>=_)
open import Data.String using (String; toVec; _==_; strictTotalOrder)
                        renaming (_++_ to _∥_)
open import Data.Product using (_×_; _,_; proj₁)
open import Coinduction
open import IO

open import Relation.Binary
open StrictTotalOrder Data.String.strictTotalOrder renaming (compare to str_cmp)

data Order : Set where
  LT EQ GT : Order

module InsertionSort where
  insert : {A : Set} → (A → A → Order) → A → List A → List A
  insert _   e []       = e ∷ []
  insert cmp e (l ∷ ls) with cmp e l
  ... | GT = l ∷ insert cmp e ls
  ... | _  = e ∷ l ∷ ls

  sort : {A : Set} → (A → A → Order) → List A → List A
  sort cmp = foldr (insert cmp) []
open InsertionSort using (insert; sort)


-- Universe U exists of type U and el : U → Set
data U : Set where
  CHAR NAT BOOL : U
  VEC  : U → ℕ → U
  
el : U → Set
el CHAR      = Char
el NAT       = ℕ
el (VEC u n) = Vec (el u) n
el BOOL      = Bool

parens : String → String
parens str = "(" ∥ str ∥ ")"

show : {u : U} → el u → String
show {CHAR         } c        = charToString c
show {NAT          } zero     = "Zero"
show {NAT          } (suc k)  = "Succ " ∥ parens (show k)
show {VEC u zero   } Nil      = "Nil"
show {VEC u (suc k)} (x ∷ xs) = parens (show x) ∥ " ∷ " ∥ parens (show xs)
show {BOOL         } true     = "True"
show {BOOL         } false    = "False"

_=ᴺ_ : ℕ → ℕ → Bool
zero  =ᴺ zero  = true
suc m =ᴺ suc n = (m =ᴺ n)
_     =ᴺ _     = false

_≤ᴺ_ : ℕ → ℕ → Order
zero  ≤ᴺ zero  = EQ
zero  ≤ᴺ _     = LT
_     ≤ᴺ zero  = GT
suc a ≤ᴺ suc b = a ≤ᴺ b

_=ᵁ_ : U → U → Bool
CHAR    =ᵁ CHAR      = true
NAT     =ᵁ NAT       = true
BOOL    =ᵁ BOOL      = true
VEC u x =ᵁ VEC u' x' = (u =ᵁ u') ∧ (x =ᴺ x')
_       =ᵁ _         = false

_≤ᵁ_ : U → U → Order
CHAR ≤ᵁ CHAR = EQ
CHAR ≤ᵁ _ = LT
_ ≤ᵁ CHAR = GT
NAT ≤ᵁ NAT = EQ
NAT ≤ᵁ _ = LT
_ ≤ᵁ NAT = GT
BOOL ≤ᵁ BOOL = EQ
BOOL ≤ᵁ _ = LT
_ ≤ᵁ BOOL = GT
VEC a x ≤ᵁ VEC b y with a ≤ᵁ b
... | LT = LT
... | EQ = x ≤ᴺ y
... | GT = GT


So : Bool → Set
So true  = ⊤
So false = ⊥

data SqlValue : Set where
  SqlString  : String → SqlValue
  SqlChar    : Char   → SqlValue
  SqlBool    : Bool   → SqlValue
  SqlInteger : ℤ      → SqlValue
--{-# COMPILED_DATA SqlValue SqlValue SqlString SqlChar SqlBool SqlInteger #-}

module OrderedSchema where
  SchemaDescription = List (List SqlValue)

  Attribute : Set
  Attribute = String × U

  -- Compare on type if names are equal.
  -- SQL DB's probably don't allow columns with the same name
  -- but nothing prevents us from writing a Schema that does,
  -- this is necessary to make our sort return a unique answer.
  attr_cmp : Attribute → Attribute → Order
  attr_cmp (nm₁ , U₁) (nm₂ , U₂) with str_cmp nm₁ nm₂ | U₁ ≤ᵁ U₂
  ... | tri< _ _ _ | _     = LT
  ... | tri≈ _ _ _ | U₁≤U₂ = U₁≤U₂
  ... | tri> _ _ _ | _     = GT


  data Schema : Set where
    sorted : List Attribute → Schema

  mkSchema : List Attribute → Schema
  mkSchema xs = sorted (sort attr_cmp xs)

  expandSchema : Attribute → Schema → Schema
  expandSchema x (sorted xs) = sorted (insert attr_cmp x xs)

  schemify : SchemaDescription → Schema
  schemify sdesc = {!!}


  disjoint : Schema → Schema → Bool
  disjoint (sorted []      ) (_              ) = true
  disjoint (_              ) (sorted []      ) = true
  disjoint (sorted (x ∷ xs)) (sorted (y ∷ ys)) with attr_cmp x y
  ... | LT = disjoint (sorted xs      ) (sorted (y ∷ ys))
  ... | EQ = false
  ... | GT = disjoint (sorted (x ∷ xs)) (sorted ys      )

  sub : Schema → Schema → Bool
  sub (sorted []      ) (_              ) = true
  sub (sorted (x ∷ _) ) (sorted []      ) = false
  sub (sorted (x ∷ xs)) (sorted (X ∷ Xs)) with attr_cmp x X
  ... | LT = false
  ... | EQ = sub (sorted xs      ) (sorted Xs)
  ... | GT = sub (sorted (x ∷ xs)) (sorted Xs)

  same' : List Attribute → List Attribute → Bool
  same' ([]              ) ([]              ) = true
  same' ((nm₁ , ty₁) ∷ xs) ((nm₂ , ty₂) ∷ ys) =
    (nm₁ == nm₂) ∧ (ty₁ =ᵁ ty₂) ∧ same' xs ys
  same' (_               ) (_               ) = false

  same : Schema → Schema → Bool
  same (sorted xs) (sorted ys) = same' xs ys

  occurs : String → Schema → Bool
  occurs nm (sorted s) = any (_==_ nm) (map (proj₁) s)

  lookup' : (nm : String) → (s : List Attribute)
              → So (occurs nm (sorted s)) → U
  lookup' _  []                   ()
  lookup' nm ((name , type) ∷ s') p with nm == name
  ... | true  = type
  ... | false = lookup' nm s' p

  lookup : (nm : String) → (s : Schema) → So (occurs nm s) → U
  lookup nm (sorted s) = lookup' nm s

  append : (s s' : Schema) → Schema
  append (sorted s) (sorted s') = mkSchema (s ++ s')
open OrderedSchema using (Schema; mkSchema; expandSchema; schemify;
                          disjoint; sub; same; occurs; lookup;
                          append)


data Row : Schema → Set where
  EmptyRow : Row (mkSchema [])
  ConsRow  : ∀ {name u s} → el u → Row s → Row (expandSchema (name , u) s)

Table : Schema → Set
Table s = List (Row s)

DatabasePath = String
TableName    = String

postulate
  Connection : Set
  connectSqlite3 : DatabasePath → IO Connection
  describe_table : TableName → Connection → IO (List (List SqlValue))
-- {-# COMPILED_TYPE Connection Connection #-}
-- {-# COMPILED connectSqlite3 connectSqlite3 #-}
-- {-# COMPILED describe_table describe_table #-}


data Handle : Schema → Set where
  conn : Connection → (s : Schema) → Handle s

-- Connect currently ignores differences between
-- the expected schema and the actual schema.
-- According to tpop this should result in
-- "a *runtime exception* in the *IO* monad."
-- Agda does not have exceptions(?)
--  -> postulate error with a compiled pragma?
connect : DatabasePath → TableName → (s : Schema) → IO (Handle s)
connect DB table schema_expect =
  ♯ (connectSqlite3 DB) >>=
    (λ sqlite_conn →
      ♯ (♯ (describe_table table sqlite_conn) >>=
      (λ description →
        ♯ (♯ (return (schemify description)) >>=
        (λ schema_actual →
          ♯ (♯ (return (same schema_expect schema_actual)) >>=
          (λ { true  → ♯ (return (conn sqlite_conn schema_expect));
               false → ♯ (return (conn sqlite_conn schema_expect)) })))))))


data Expr : Schema → U → Set where
  equal    : ∀ {u s} → Expr s u → Expr s u → Expr s BOOL
  lessThan : ∀ {u s} → Expr s u → Expr s u → Expr s BOOL
  _!_      : (s : Schema) → (nm : String) → {p : So (occurs nm s)}
               → Expr s (lookup nm s p)


data RA : Schema → Set where
  Read    : ∀ {s} → Handle s → RA s
  Union   : ∀ {s} → RA s → RA s → RA s
  Diff    : ∀ {s} → RA s → RA s → RA s
  Product : ∀ {s s'} → {_ : So (disjoint s s')} → RA s → RA s'
              → RA (append s s')
  Project : ∀ {s} → (s' : Schema) → {_ : So (sub s' s)} → RA s → RA s'
  Select  : ∀ {s} → Expr s BOOL → RA s → RA s
  -- ...
{- 
  As we mentioned previously, we have taken a very minimal set of relational
  algebra operators. It should be fairly straightforward to add operators
  for the many other operators in relational algebra, such as the

  natural join, θ-join, equijoin, renaming, or division,

  using the same techniques. Alternatively, you can define many of these
  operations in terms of the operations we have implemented in the RA data type.
-}


-- We could:
postulate
  toSQL : ∀ {s} → RA s → String

-- We can do much better:
postulate
  query : {s : Schema} → RA s → IO (List (Row s))
{-
  The *query* function uses *toSQL* to produce a query, and passes this to the
  database server. When the server replies, however, we know exactly how to
  parse the response: we know the schema of the table resulting from our query,
  and can use this to parse the database server's response in a type-safe
  manner. The type checker can then statically check that the program uses the
  returned list in a way consistent with its type.
-}


Cars : Schema
Cars = mkSchema (("Model" , VEC CHAR 20) ∷ ("Time" , VEC CHAR 6)
                 ∷ ("Wet" , BOOL) ∷ [])

zonda : Row Cars
zonda = ConsRow (toVec "Pagani Zonda C12 F  ")
        (ConsRow (toVec "1:18.4")
        (ConsRow false EmptyRow))

Models : Schema
Models = mkSchema (("Model" , VEC CHAR 20) ∷ [])

models : Handle Cars → RA Models
models h = Project Models (Read h)

wet : Handle Cars → RA Models
wet h = Project Models (Select (Cars ! "Wet") (Read h))


{- Discussion
   ==========

   There are many, many aspects of this proposal that can be improved. Some
   attributes of a schema contain *NULL*-values; we should close our universe
   under *Maybe* accordingly. Some database servers silently truncate strings
   longer than 255 characters. We would do well to ensure statically that this
   never happens. Our goal, however, was not to provide a complete model of all
   of SQL's quirks and idiosyncrasies: we want to show how a language with
   dependent types can schine where Haskell struggles.
     Our choice of *Schema* data type suffers from the usual disadvantages of
   using a list to represent a set: our *Schema* data type may contain
   duplicates and the order of the elements matters. The first problem is easy
   to solve. Using an implicit proof argument in the *Cons* case, we can define
   a data type for lists that do not contain duplicates. The type of *Cons* then
   becomes:
     Cons : (nm : String) → (u : U) → (s : Schema) → {_ : So (not (elem nm s))}
                → Schema
   The second point is a bit trickier. The real solution would involve quotient
   types to make the order of the elements unobservable. As Agda does not
   support quotient types, however, the best we can do is parameterise our
   constructors by an additional proof argument, when necessary. For example,
   the *Union* constructor could be defined as follows:
     Union : ∀ {s s'} → {_ : So (permute s s')} → RA s → RA s' → RA s
   Instead of requiring that both arguments of *Union* are indexed by the same
   schema, we should only require that the two schemas are equal up to a
   permutation of the elements. Alternatively, we could represent the *Schema*
   using a data structure that fixes the order in which its constituent
   elements occur, such as a trie or sorted list.
     Finally, we would like to return to our example table. We chose to model
   the lap time as a fixed-length string ─ clearly, a triple of integers would
   be a better representation. Unfortunately, most database servers only
   support a handful of built-in types, such as strings, numbers, bits. There
   is no way to extend these primitive types. This problem is sometimes
   referred to as the *object-relational impedance mismatch*. We believe the
   generic programming techniques and views from the previous sections can be
   used to marshall data between a low-level representation in the database
   and the high-level representation in our programming language.
-}
