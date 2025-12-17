-- |
--
-- Module      : Math.DyckWord.Binary
-- Copyright   : (c) 2017 Johannes Hildén
-- License     : BSD3
-- Maintainer  : hildenjohannes@gmail.com
-- Stability   : experimental
-- Portability : GHC
--
-- == Background
--
-- In formal language theory, the /Dyck language/ consists of all strings of 
-- evenly balanced left and right parentheses, brackets, or some other 
-- symbols, together with the /empty/ word. Words in this language (named 
-- after German mathematician Walther von Dyck) are known as /Dyck words/, 
-- some examples of which are @()()()@, @(())((()))@, and @((()()))()@.
--
-- The type of Dyck language considered here is defined over a binary alphabet. 
-- We will take this alphabet to be the set &#931; = {(, )} in the following 
-- examples. The binary Dyck language is the subset of &#931;* (the Kleene 
-- closure of &#931;) of all words that satisfy two conditions:
-- 
-- 1. The number of left brackets must be the same as the number of right 
--    brackets.
-- 2. Going from left to right, for each character read, the total number of 
--    right brackets visited must be less than or equal to the number of left 
--    brackets up to the current position.
--
-- E.g., @(()(()@ and @())(())()@ are __not__ Dyck words.
--
-- When regarded as a combinatorial class&#8212;with the 'size' of a word defined as 
-- the number of bracket pairs it contains&#8212;the counting sequence associated 
-- with the Dyck language is the /Catalan numbers/.
--
-- \[ 
--    \begin{array}{ccl}
--      \text{Size} & \text{Count} & \text{Words}
--      \\
--      0 & 1   & \epsilon
--      \\
--      1 & 1   & ⟨⟩
--      \\
--      2 & 2   & ⟨⟩⟨⟩, \ ⟨⟨⟩⟩
--      \\
--      3 & 5   & ⟨⟩⟨⟩⟨⟩, \ ⟨⟩⟨⟨⟩⟩, \ ⟨⟨⟩⟩⟨⟩, \ ⟨⟨⟩⟨⟩⟩, \ ⟨⟨⟨⟩⟩⟩
--      \\
--      4 & 14  & ⟨⟩⟨⟩⟨⟩⟨⟩, \ ⟨⟩⟨⟩⟨⟨⟩⟩, \ ⟨⟩⟨⟨⟩⟩⟨⟩, \ ⟨⟩⟨⟨⟩⟨⟩⟩, \ ⟨⟩⟨⟨⟨⟩⟩⟩, \ ⟨⟨⟩⟩⟨⟩⟨⟩, \ ⟨⟨⟩⟩⟨⟨⟩⟩, \ ⟨⟨⟩⟨⟩⟩⟨⟩,
--      \\
--        &     & ⟨⟨⟨⟩⟩⟩⟨⟩, \ ⟨⟨⟩⟨⟩⟨⟩⟩, \ ⟨⟨⟩⟨⟨⟩⟩⟩, \ ⟨⟨⟨⟩⟩⟨⟩⟩, \ ⟨⟨⟨⟩⟨⟩⟩⟩, \ ⟨⟨⟨⟨⟩⟩⟩⟩
--      \\
--      5 & 42  & ⟨⟩⟨⟩⟨⟩⟨⟩⟨⟩, \ ⟨⟩⟨⟩⟨⟩⟨⟨⟩⟩, \ ⟨⟩⟨⟩⟨⟨⟩⟩⟨⟩, \ ⟨⟩⟨⟩⟨⟨⟩⟨⟩⟩, \ ⟨⟩⟨⟩⟨⟨⟨⟩⟩⟩, \ \dots, \ ⟨⟨⟨⟨⟨⟩⟩⟩⟩⟩
--      \\
--      6 & 132 & \dots
--    \end{array}
-- \]

module Math.DyckWord.Binary ( 
  -- * Types
    Size
  , Rank
  , DyckWord
  -- * Creating and inspecting Dyck words
  , empty
  , size 
  , setAlphabet
  , concatWords 
  -- ** Textual form
  , fromText 
  , fromText'
  , toText
  -- * Ranking and unranking
  -- $ranking
  , rank 
  , rankRelative 
  , unrank 
  , unrankRelative 
  , unrankRelative'
  , wordsOfSize 
  ) where

import Control.Applicative                 ( (<$>) )
import Data.Maybe                          ( fromJust )
import Data.Monoid
import Data.Text                           ( Text, unfoldrN )
import Math.DyckWord.Binary.Internal

import qualified Data.Text                 as T

-- $ranking
--
-- To /rank/ a Dyck word is to determine its position in some ordered sequence 
-- of words. The dual of this&#8212;to produce the Dyck word corresponding to a 
-- position in said sequence&#8212;is called /unranking/. The order we are 
-- interested in here is known as /shortlex/, and it demands that a smaller 
-- Dyck word always gets precedence over a bigger one. When comparing words of 
-- the same size, normal lexicographical order applies. 
--
-- === Relative vs. absolute rank
--
-- In this library, we adopt the following (non-standard) terminology.
-- The /relative/ rank of a Dyck word /w/ is its position in the sequence of 
-- those words with the same size as /w/. By contrast, the /absolute/ rank 
-- means a word's position in the shortlex sequence of __all__ Dyck words.
-- /For example:/ The (absolute) rank of @(((())))@ is 9, but the relative rank 
-- of the same word is 0, since it is the first word of size four.
--
-- \[
--    \begin{array}{lccc}
--      \text{Word} & \text{Size} & \text{Rank} & \text{Relative rank}
--      \\
--      \epsilon & 0 & 0 & 0 \\
--      ⟨⟩       & 1 & 1 & 0 \\
--      ⟨⟨⟩⟩     & 2 & 2 & 0 \\
--      ⟨⟩⟨⟩     & 2 & 3 & 1 \\
--      ⟨⟨⟨⟩⟩⟩   & 3 & 4 & 0 \\
--      ⟨⟨⟩⟨⟩⟩   & 3 & 5 & 1 \\
--      ⟨⟨⟩⟩⟨⟩   & 3 & 6 & 2 \\
--      ⟨⟩⟨⟨⟩⟩   & 3 & 7 & 3 \\
--      ⟨⟩⟨⟩⟨⟩   & 3 & 8 & 4 \\
--      ⟨⟨⟨⟨⟩⟩⟩⟩ & 4 & 9 & 0 \\
--      ⟨⟨⟨⟩⟨⟩⟩⟩ & 4 & 10 & 1 \\
--      \;\;\;\; \vdots & \vdots & \vdots & \vdots
--    \end{array}
-- \]
--
-- If we let \(r(w)\) denote the relative rank of a word \(w\), and \(C_i\) the 
-- \(i^{th}\) Catalan number, then the absolute rank \(R(w)\) of \(w\) is given 
-- by the formula \( R(w) = r(w) + \sum_{i=0}^{s-1} C_i, \) where \(s\) is the 
-- size of \(w\).

-- | See 'size'.
type Size = Integer

-- | Represents the /rank/ of a Dyck word.
type Rank = Integer

-- | Opaque Dyck word type. For functions to build Dyck words, see:
--
--     * 'empty', 
--     * 'fromText', 
--     * 'fromText'', 
--     * 'unrank', 
--     * 'unrankRelative', and 
--     * 'unrankRelative''.
--
-- Conceptually, every non-empty Dyck word has the form /(a)b/, where /a/ and
-- /b/ are Dyck words. The BNF grammar for this language is given by 
-- \( \omega = \epsilon \mid ( \omega ) \omega \).
data DyckWord = DyckWord 
  { _size    :: !Size
  , _absRank :: !Rank
  , _relRank :: !Rank
  , _text    :: !Text
  } deriving (Show)

-- | Two Dyck words are considered equal when they have the same /absolute/
--   rank. 
-- 
-- >>> fromText' "010011000111" == fromText' "xyxxyyxxxyyy"
-- True
instance Eq DyckWord where
  a == b = _absRank a == _absRank b

-- | Dyck words of the same size are ordered lexicographically, and a smaller 
--   Dyck word always gets precedence over a bigger one.
--
-- >>> fromText' "0011" < fromText' "0101"
-- True
--
-- >>> fromText' "0101" > fromText' "01"
-- True
instance Ord DyckWord where
  a <= b = _absRank a <= _absRank b

-- | The /empty/ Dyck word.
empty :: DyckWord
empty = DyckWord 
  { _size    = 0
  , _absRank = 0
  , _relRank = 0
  , _text    = T.empty } 

-- | The /size/ of a Dyck word is the number of bracket pairs it contains, 
--   i.e., half of the length of the word's string representation. Inductively, 
--   it can be defined as
--
-- \[ 
--    \text{size}\;w = 
--      \begin{cases}
--        0 && \text{if} \; w = \epsilon \\
--        1 + \text{size}\;u + \text{size}\;v && \text{if} \; w = (u)v.  
--      \end{cases}
-- \]
size :: DyckWord -> Size
size = _size

juxtapose :: DyckWord -> DyckWord -> Text
juxtapose a b 
    | compatible = _text a <> _text b
    | otherwise  = _text a <> _text (setAlphabet (firstChar a) (finalChar a) b)
  where
    firstChar = T.head . _text
    finalChar = T.last . _text
    compatible 
      | 0 == _absRank a = True
      | 0 == _absRank b = True
      | otherwise = firstChar a == firstChar b && finalChar a == finalChar b

-- | Change the alphabet of a Dyck word. An alphabet has two characters, here
--   referred to as the /left/ and /right/ symbol, respectively. For example:
--
-- >>> toText (setAlphabet 'x' 'o' (unrank 55))
-- xoxxoxxooo
setAlphabet :: Char       -- ^ Left symbol
            -> Char       -- ^ Right symbol
            -> DyckWord 
            -> DyckWord
setAlphabet a' b' w = w { _text = f `T.map` t }
  where
    t = _text w
    a = T.head t
    b = T.last t
    f c | c == a = a'
        | c == b = b'
        | otherwise = error "not a valid dyck word"

-- | Concatenate two Dyck words. Corresponds to ordinary string concatenation.
--
-- \[ 
--    \begin{align}
--      \epsilon +\!\!\!+\;w &= w 
--      \\
--      (u)v     +\!\!\!+\;w &= (u)[ v +\!\!\!+\; w ]
--    \end{align}
-- \]
--
-- If the two words have different alphabets, the concatenated word will 
-- inherit the first word's symbol set.
concatWords :: DyckWord -> DyckWord -> DyckWord
concatWords a b = fromText' (juxtapose a b)

-- | The Dyck language forms a semigroup under 'concatWords'.
instance Semigroup DyckWord where
  (<>) = concatWords

-- | The Dyck language forms a monoid under 'concatWords', with the 'empty'
--   word as identity.
instance Monoid DyckWord where
  mappend = (<>)
  mempty = empty

-- | Return the /absolute/ rank of a Dyck word. That is, its position in the 
--   (shortlex) ordered sequence of /all/ Dyck words.
rank :: DyckWord -> Rank
rank = _absRank

-- | Return the /relative/ rank of a Dyck word. 
rankRelative :: DyckWord -> Rank
rankRelative = _relRank

-- | Parse a 'Text' value to a 'DyckWord'. The result is wrapped in a 'Maybe', 
--   so that the value becomes 'Nothing' if parsing fails. The alphabet is 
--   determined by looking at the first and last characters of the input.
fromText :: Text -> Either String DyckWord
fromText t 
    | T.null t  = Right empty
    | odd len   = Left "odd length input"
    | a == b    = err
    | otherwise = case T.foldr f (Right (0, s, s)) (T.reverse t) of
        Left e -> Left e
        Right (r,_,_) -> Right $ DyckWord 
          { _size    = s
          , _absRank = catalanSum (fromIntegral s) + r
          , _relRank = r
          , _text    = t } 
  where
    a = T.head t
    b = T.last t
    s = fromIntegral (len `div` 2)
    len = T.length t
    err = Left "bad input"
    f c (Right (i, x, y))
      | x > y || x < 0 = err
      | c == a = Right (i, x - 1, y)
      | c == b = Right (i + catalanTriangle y (x - 1), x, y - 1)
    f _ _ = err

-- | Parse a 'Text' value to a 'DyckWord'. Throws an error if parsing fails.
--   This is an unsafe version of 'fromText'.
fromText' :: Text -> DyckWord
fromText' t = 
    case fromText t of
      Right r -> r 
      Left  _ -> error "not a valid dyck word"

-- | Return a textual representation of a 'DyckWord'.
toText :: DyckWord -> Text
toText = _text

-- | Return the /n/-th Dyck word in the (shortlex) ordered sequence of /all/
--   Dyck words. 
unrank :: Rank -> DyckWord 
unrank r 
    | r < 0 = error "rank cannot be negative"
    | otherwise = unrankRelative' s i
  where
    (s, i) = sizeOffs r 0 

sizeOffs :: Integral a => Integer -> a -> (a, Integer)
sizeOffs n x 
    | n < c     = (x, n)
    | otherwise = sizeOffs (n - c) (x + 1) 
  where 
    c = catalan (fromIntegral x)

-- | Return the /n/-th Dyck word, restricted to only words of a given size.
--   Words are lexicographically ordered. The result is wrapped in a 'Maybe', 
--   and is equal to 'Nothing' if the given rank is outside of the valid range. 
unrankRelative :: Size -> Rank -> Maybe DyckWord 
unrankRelative s r 
    | r < 0 
   || r >= catalan s = Nothing
    | otherwise    = Just DyckWord 
        { _size    = s
        , _absRank = offset + r
        , _relRank = r
        , _text    = t } 
  where 
    t = unfoldrN (fromIntegral (2*s)) f (r, s, s)
    offset = catalanSum (fromIntegral s)
    f (i, x, y) 
        | 0 == y    = Nothing 
        | j >= 0    = Just (')', (j, x, y - 1))
        | otherwise = Just ('(', (i, x - 1, y)) 
      where 
        j = i - catalanTriangle y (x - 1) 

-- | Unsafe version of 'unrankRelative'. This function throws an error if the 
--   given rank is outside of the valid range. 
unrankRelative' :: Size -> Rank -> DyckWord
unrankRelative' s = fromJust . unrankRelative s

-- | Return a lexicographically ordered list with all Dyck words of a specific 
--   size.
wordsOfSize :: Size -> [DyckWord]
wordsOfSize = ofSize unrankRelative' 

ofSize :: (Size -> Integer -> b) -> Size -> [b]
ofSize f s = f s <$> [0 .. catalan (fromIntegral s) - 1]
