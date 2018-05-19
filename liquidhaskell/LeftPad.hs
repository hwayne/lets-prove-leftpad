{-@ LIQUID "--reflection"  @-}
{-@ LIQUID "--ple"         @-}
{-@ infixr ++              @-}
{-@ infixr !!              @-}

module PadLeft where

import Prelude hiding (max, replicate, (++), (!!))

-------------------------------------------------------------------------------
-- | Implementation
-------------------------------------------------------------------------------

{-@ reflect leftPad @-}
{-@ leftPad :: n:Int -> c:a -> xs:[a] ->
                {res:[a] | size res = max n (size xs)}
  @-}
leftPad n c xs
  | 0 < k     = replicate k c ++ xs
  | otherwise = xs
  where
    k         = n - size xs

{-@ measure size @-}
{-@ size :: [a] -> Nat @-}
size []     = 0
size (x:xs) = 1 + size xs


{-@ reflect ++ @-}
{-@ (++) :: xs:[a] -> ys:[a] -> {v:[a] | size v = size xs + size ys} @-}
[]     ++ ys = ys
(x:xs) ++ ys = x : (xs ++ ys)


{-@ reflect replicate @-}
{-@ replicate :: n:Nat -> a -> {v:[a] | size v = n} @-}
replicate :: Int -> a -> [a]
replicate 0 _ = []
replicate n c = c : replicate (n - 1) c

-------------------------------------------------------------------------------
-- | Proving the "Obviously Correct" Specification 
-------------------------------------------------------------------------------

{-@ leftPadObviousThm :: n:Int -> c:a -> xs:[a] ->
      { leftPad n c xs = if (size xs < n)
                         then (replicate (n - size xs) c ++ xs)
                         else xs }
  @-}
leftPadObviousThm _ _ _ = ()


-------------------------------------------------------------------------------
-- | Reasoning about Sequences
-------------------------------------------------------------------------------

-- **Indexing into a Sequence**

{-@ reflect !! @-}
{-@ (!!) :: xs:[a] -> {n:Nat | n < size xs} -> a @-}
(x:_)  !! 0 = x
(_:xs) !! n = xs !! (n - 1)


-- **Replicated Sequences**

{-@ thmReplicate :: n:Nat -> c:a -> i:{Nat | i < n} ->
                    { replicate n c !! i  == c }
  @-}
thmReplicate n c i
  | i == 0    = ()
  | otherwise = thmReplicate (n - 1) c (i - 1)


-- **Concatenating Sequences**

{-@ thmAppLeft :: xs:[a] -> ys:[a] -> {i:Nat | i < size xs} ->
                  { (xs ++ ys) !! i == xs !! i }
  @-}
thmAppLeft (x:xs) ys 0 = ()
thmAppLeft (x:xs) ys i = thmAppLeft xs ys (i-1)

{-@ thmAppRight :: xs:[a] -> ys:[a] -> {i:Nat | size xs <= i} ->
                   { (xs ++ ys) !! i == ys !! (i - size xs) }
  @-}
thmAppRight []     ys i = ()
thmAppRight (x:xs) ys i = thmAppRight xs ys (i-1)

-------------------------------------------------------------------------------
-- | Proving Hillel's Specification
-------------------------------------------------------------------------------
{-@ thmLeftPad
      :: n:_ -> c:_ -> xs:{size xs < n} -> i:{Nat | i < n} ->
         { (leftPad n c xs !! i) == (if (i < n - size xs) then c else (xs !! (i - (n - size xs)))) }
  @-}
thmLeftPad n c xs i
  | i < k     = thmAppLeft  cs xs i `seq` thmReplicate k c i
  | otherwise = thmAppRight cs xs i
  where
    k         = n - size xs
    cs        = replicate k c

-------------------------------------------------------------------------------
-- | Haskell sigs moved to avoid clutter 
-------------------------------------------------------------------------------

(!!)              :: [a] -> Int -> a
size              :: [a] -> Int
(++)              :: [a] -> [a] -> [a]
leftPadObviousThm :: Int -> a -> [a] -> ()
thmReplicate      :: Int -> a -> Int -> ()
thmAppLeft        :: [a] -> [a] -> Int -> ()
thmAppRight       :: [a] -> [a] -> Int -> ()
thmLeftPad        :: Int -> a -> [a] -> Int -> ()
leftPad           :: Int -> a -> [a] -> [a]

{-@ reflect max @-}
max :: Int -> Int -> Int
max x y = if x > y then x else y

