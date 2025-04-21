{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Data.Kind
import Data.Proxy (Proxy(..))
import GHC.TypeLits ( KnownSymbol, Symbol, UnconsSymbol, ConsSymbol, symbolVal
                    , AppendSymbol, TypeError, ErrorMessage(..), Nat )
import Data.Type.Bool( type (&&), If )
import Data.Type.Equality ( type (==) )
import GHC.TypeNats

{-@ The `Symbol` from GHC.TypeLits works as the type-level string
    and we exploit the following Symbol manipulation type families

    type family ConsSymbol (a :: Char) (b :: Symbol) :: Symbol
    type family AppendSymbol (a :: Symbol) (b :: Symbol) :: Symbol
    type family UnconsSymbol (a :: Symbol) :: Maybe (Char, Symbol)
@-}

-- | A type-level replicate function
type family Replicate (n :: Nat) (c :: Char) :: Symbol where
  Replicate 0 c = ""
  Replicate n c = ConsSymbol c (Replicate (n - 1) c)

-- | A type-level computation of the pad value
type family PadK (n :: Nat) (strlen :: Nat) :: Nat where
  PadK n strlen = If (n <=? strlen) 0 (n - strlen)

-- | Use `AppendSymbol` to append the pad string
--   internally using Replicate and PadK
type family PrependReplicate (c :: Char)     (n :: Nat)
                             (strlen :: Nat) (s :: Symbol) :: Symbol where
  PrependReplicate c n strlen s = AppendSymbol (Replicate (PadK n strlen) c) s



-- | We will now verify the properties; first we need a type-level assertion

type family Assert (cond :: Bool) (msg :: ErrorMessage) :: Constraint where
  Assert 'True  _   = ()
  Assert 'False msg = TypeError msg



-- | Spec 1: "The length of the output is max(n, len(str))"

type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = If (a <=? b) b a

-- | Type-level symbol length
type family Length (p :: Symbol) :: Nat where
  Length "" = 0
  Length s  = 1 + Length (TailSymbol s)

-- | Spec 1 verbatim
type family PadKMaxEqual (n :: Nat) (strlen :: Nat) (full :: Symbol) :: Bool where
  PadKMaxEqual n strlen full = Length full == Max n strlen

-- | Compile time check that padded string length = max (n, strlen)
type PadKMaxEqualConstraint (n :: Nat) (strlen :: Nat) (full :: Symbol) =
  Assert (PadKMaxEqual n strlen full)
    ( 'Text    "PadKMaxEqual failed: (PadK "
   ':<>: 'ShowType n
   ':<>: 'Text    " "
   ':<>: 'ShowType strlen
   ':<>: 'Text    ") + "
   ':<>: 'ShowType strlen
   ':<>: 'Text    " /= Max "
   ':<>: 'ShowType n
   ':<>: 'Text    " "
   ':<>: 'ShowType strlen
    )



-- | Spec 2: "The prefix of the output is padding characters
--            and nothing but padding characters"

-- | Prefix test - uses UnconsSymbol for deconstructing the string
type family IsPrefix (p :: Symbol) (s :: Symbol) :: Bool where
  IsPrefix "" s  = 'True
  IsPrefix p  "" = 'False
  IsPrefix p  s = IsPrefixRec (UnconsSymbol p) (UnconsSymbol s)

-- | Auxiliary family doing the character‐by‐character test
type family IsPrefixRec
  (mp :: Maybe (Char, Symbol))
  (ms :: Maybe (Char, Symbol))
  :: Bool where
  IsPrefixRec 'Nothing     _                    = 'True
  IsPrefixRec ('Just '(c, p')) ('Just '(c', s')) =
    (c == c') && IsPrefix p' s'
  IsPrefixRec _            _                    = 'False

-- | Compile time check that `s` starts with `p`
type PrefixConstraint (p :: Symbol) (s :: Symbol) =
  Assert (IsPrefix p s)
    ( 'Text    "Symbol "
   ':<>: 'ShowType s
   ':<>: 'Text    " does not start with "
   ':<>: 'ShowType p
    )

-- | Check for if the prefix is by the correct pad value
type PrefixedByReplicate (c :: Char) (n :: Nat) (strlen :: Nat) (full :: Symbol) =
  PrefixConstraint (Replicate (PadK n strlen) c) full

-- | The actual validation that the newly‑built symbol actually has the right prefix.
type ValidatePrepend (c :: Char) (n :: Nat) (strlen :: Nat) (full :: Symbol) =
  PrefixedByReplicate c n strlen full



-- | Spec 3: "The suffix of the output is the original string"

-- | Type-level string utils
type family TailSymbol (s :: Symbol) :: Symbol where
  TailSymbol s = TailSymbolRec (UnconsSymbol s)

type family TailSymbolRec (m :: Maybe (Char, Symbol)) :: Symbol where
  TailSymbolRec 'Nothing          = ""
  TailSymbolRec ('Just '(c, cs))  = cs

type family Drop (n :: Nat) (s :: Symbol) :: Symbol where
  Drop 0 s = s
  Drop n s = Drop (n - 1) (TailSymbol s)

-- | Suffix check
type family IsSuffix (s :: Symbol) (full :: Symbol) :: Bool where
  IsSuffix s full = s == Drop (Length full - Length s) full

-- | Ensure at compile time that `p` is a suffix of `s`
type SuffixConstraint (s :: Symbol) (full :: Symbol) =
  Assert (IsSuffix s full)
    ( 'Text    "Symbol "
   ':<>: 'ShowType full
   ':<>: 'Text    " does not end with "
   ':<>: 'ShowType s
    )

-- | The actual validation that the newly‑built symbol actually has the right suffix.
type ValidateSuffix s full = SuffixConstraint s full



-- | Putting Specs 1, 2, and 3 together
leftPad :: forall c n s strlen full.
           ( full ~ PrependReplicate c n strlen s -- like a type-level `let`
           , PadKMaxEqualConstraint n strlen full -- Spec 1
           , ValidatePrepend c n strlen full      -- Spec 2
           , ValidateSuffix  s full               -- Spec 3
           , KnownSymbol full -- used for `reifying` the type-level symbol
           )
        => Proxy s
        -> Proxy strlen
        -> String
leftPad _ _ = symbolVal (Proxy @full)


-- | Tests
test1, test2, test3, test4 :: String
test1 = leftPad @'!' @7 (Proxy @"abc") (Proxy @3)
test2 = leftPad @'!' @3 (Proxy @"xyz") (Proxy @3)
test3 = leftPad @'!' @5 (Proxy @"foo") (Proxy @3)
test4 = leftPad @'!' @0 (Proxy @"foo") (Proxy @3)

main :: IO ()
main = do
  putStrLn test1
  putStrLn test2
  putStrLn test3
  putStrLn test4
