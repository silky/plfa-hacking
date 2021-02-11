module hello-world where

open import IO
open import Data.Nat


ten = 10

-- Hello
--
-- main = run ( putStrLn "Hello, World!" )


data Greeting : Set where
  hello : Greeting

greet : Greeting
greet = hello
