{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Main where

import Data.Maybe (fromJust)
import Data.Proxy (Proxy(..))
import GHC.TypeLits (Nat, type (<=?), KnownNat)
import Data.Type.Bool (If)
import GHC.TypeNats
import qualified Data.Vector.Sized as V


type family Max (a :: Nat) (b :: Nat) :: Nat where
  Max a b = If (a <=? b) b a

type family PadK (pad :: Nat) (n :: Nat) :: Nat where
  PadK pad n = If (pad <=? n) 0 (pad - n)

padString :: forall (pad :: Nat) (n :: Nat).
             (KnownNat pad, KnownNat n, KnownNat (PadK pad n))
           => Proxy pad
           -> Proxy n
           -> Char
           -> V.Vector (PadK pad n) Char
padString _ _ c = V.replicate c

-- The key trick
class ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual (pad :: Nat) (n :: Nat)
instance ((PadK pad n) + n ~ Max pad n) => PadKMaxEqual pad n


leftPad :: forall (pad :: Nat) (n :: Nat).
           (KnownNat pad, KnownNat n, KnownNat (PadK pad n), PadKMaxEqual pad n)
         => Char                           -- Padding character
         -> Proxy pad                      -- Length with padding
         -> V.Vector n Char                -- The original vector (length n)
         -> V.Vector (Max pad n) Char      -- Result: padded to max(n, pad)
leftPad c pPad str = (padString pPad (proxyN str) c) V.++ str
  where
    proxyN :: KnownNat n => V.Vector n a -> Proxy n
    proxyN _ = Proxy

example = leftPad '!' (Proxy @5) getStr
  where
    myStr  = V.fromList "foo" :: Maybe (V.Vector 3 Char)
    getStr = fromJust myStr

main :: IO ()
main = putStrLn $ show example
