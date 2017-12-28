{-# LANGUAGE NPlusKPatterns #-}
-- |
-- 第3章 型無し算術式
module Language.TAPL.Chap03 (
  -- * 3.1 導入
   Term (..)
  -- * 3.2 構文
  ,setl
  ,set
  ,term
  -- * 3.3 項に関する帰納法
  ,consts
  ,size
  ,depth
  -- * 3.4 意味論のスタイル
  -- * 3.5 評価
  -- ** ブール式
  ,bterm
  -- ** ブール値
  ,isBValue
  -- ** 推論規則
  ,eIfTrue,eIfFalse,eIf
  ,brule
  ,stepB
  -- ** ブール-数値式
  ,bnterm
  -- ** ブール-数値
  ,isNValue
  ,isBNValue
  -- ** 推論規則
  ,eSucc,ePredZero,ePredSucc,ePred,eIsZeroZero,eIsZeroSucc,eIsZero
  ,nrule
  ,stepBN
  -- ** 正規形
  ,isNormalForm
  -- ** 簡約系列
  ,transitions
  ,bigstep
  -- ** WRONGの導入
  ,isBadNValue
  ,isBadBValue
  ,eIfWrong,eSuccWrong,ePredWrong,eIsZeroWrong
  ,wrule
  ,stepW
  ,stepBNW
  -- ** 自然意味論
  ,bValue,bIfTrue,bIfFalse,bSucc,bPredZero,bPredSucc,bIsZeroZero,bIsZeroSucc
  ) where

import Control.Applicative
import Data.List (unfoldr)
import Data.Set (Set)
import qualified Data.Set as Set hiding (Set)

-- |
-- 項
--
data Term = TRUE
          | FALSE
          | ZERO
          | SUCC Term
          | PRED Term
          | IsZERO Term
          | IF Term Term Term
          | WRONG
          deriving (Eq,Ord,Show)
  
-- |
-- 項集合
--
term :: Set Term
term = set

-- |
-- 演習 3.2.4.
--
-- >>> Set.size (setl 3)
-- 59439
--
-- 演習 3.2.5.
--
-- @
-- S_0   = ∅
-- S_i+1 = f(S_i)
-- 
-- 添字上の帰納法
-- i = 0 の場合:
--      S_0 
--   ＝   { 定義 }
--      ∅
--   ⊆   { ∀S . ∅ ⊆ S だから }
--      S_1
--
-- i = n+1 の場合：
--      S_n+1
--   ＝   { 定義 }
--      f(S_n)
--   ⊆   { A ⊆ B ⇔ f(A) ⊆ f(B)および帰納法の仮定 }
--      f(S_n+1)
--   ＝   { 定義 }
--      S_n+2
-- @
--

setl :: Int -> Set Term
setl 0     = Set.empty
setl (i+1) = f (setl i)
          where
            f s = foldr1 (∪) (map ($ s) [terms0,terms1,terms3])
            terms0 _ = Set.fromList [TRUE,FALSE,ZERO]
            terms1 s = Set.fromList (concat [ [SUCC t, PRED t, IsZERO t] | t <- Set.toList s ])
            terms3 s = Set.fromList [ IF t1 t2 t3 | let s' = Set.toList s, t1 <- s', t2 <- s', t3 <- s' ]
setl _     = error "negative index"
-- |
-- 項集合の構成
--
set :: Set Term
set =  Set.unions [ setl i | i <- [0 ..]]

(∪) :: (Ord a) => Set a -> Set a -> Set a
(∪) = Set.union

-- |
-- 項に出現する定数の集合
--
consts :: Term -> Set Term
consts t@WRONG = Set.singleton t
consts t@TRUE  = Set.singleton t
consts t@FALSE = Set.singleton t
consts t@ZERO  = Set.singleton t
consts (SUCC t1) = consts t1
consts (PRED t1) = consts t1
consts (IsZERO t1)   = consts t1
consts (IF t1 t2 t3) = consts t1 ∪ consts t2 ∪ consts t3

-- |
-- 項のサイズ
--
-- @
-- consts t ≦ size t
-- @
--
size :: Term -> Int
size WRONG = 1
size TRUE  = 1
size FALSE = 1
size ZERO  = 1
size (SUCC t1)     = size t1 + 1
size (PRED t1)     = size t1 + 1
size (IsZERO t1)   = size t1 + 1
size (IF t1 t2 t3) = size t1 + size t2 + size t3 + 1

-- |
-- 項の深さ
--
-- >>> Set.findMax (Set.map depth (setl 3))
-- 3
--
depth :: Term -> Int
depth WRONG = 1
depth TRUE  = 1
depth FALSE = 1
depth ZERO  = 1
depth (SUCC t1)     = depth t1 + 1
depth (PRED t1)     = depth t1 + 1
depth (IsZERO t1)   = depth t1 + 1
depth (IF t1 t2 t3) = maximum [depth t1, depth t2, depth t3] + 1

-- |
-- ブール式
--
bterm :: Term -> Maybe Term
bterm t@TRUE        = Just t
bterm t@FALSE       = Just t
bterm (IF t1 t2 t3) = IF <$> bterm t1 <*> bterm t2 <*> bterm t3
bterm _             = Nothing

-- |
-- ブール値
isBValue :: Term -> Bool
isBValue TRUE  = True
isBValue FALSE = True
isBValue _     = False

type Rule = Term -> Maybe Term

brule :: Rule
brule t =  foldr1 (<|>) (map ($ t) [eIfTrue,eIfFalse,eIf])

eIfTrue  :: Rule
eIfTrue (IF TRUE t2 _) = Just t2
eIfTrue _              = Nothing

eIfFalse :: Rule
eIfFalse (IF FALSE _ t3) = Just t3
eIfFalse _               = Nothing

eIf      :: Rule
eIf (IF t1 t2 t3) = IF <$> stepB t1 <*> Just t2 <*> Just t3
eIf _             = Nothing

-- | スモールステップ遷移（ブール式）
stepB :: Term -> Maybe Term
stepB = brule


-- |
-- 正規形
isNormalForm :: (Term -> Maybe Term) -> Term -> Bool
isNormalForm step = maybe True (const False) . step

-- |
-- 遷移列
transitions :: (Term -> Maybe Term) -> Term -> [Term]
transitions step = (:) <*> unfoldr phi
  where
    phi t = step t >>= \ t' -> Just (t',t')

-- |
-- ビッグステップ評価
bigstep :: (Term -> Maybe Term) -> Term -> Term
bigstep step = last . transitions step
          
-- |
-- ブール-数値式
bnterm :: Term -> Maybe Term
bnterm t@TRUE        = Just t
bnterm t@FALSE       = Just t
bnterm t@ZERO        = Just t
bnterm (SUCC t)      = SUCC <$> nterm t
bnterm (PRED t)      = PRED <$> nterm t
bnterm (IsZERO t)    = IsZERO <$> nterm t
bnterm (IF t1 t2 t3) = IF <$> bterm' t1 <*> bnterm t2 <*> bnterm t3
bnterm _             = Nothing

bterm' :: Term -> Maybe Term
bterm' t = bterm t <|> iszero t

iszero :: Term -> Maybe Term
iszero (IsZERO t) = IsZERO <$> nterm t
iszero _ = Nothing

nterm :: Term -> Maybe Term
nterm t@ZERO = Just t
nterm (SUCC t) = SUCC <$> nterm t
nterm (PRED t) = PRED <$> nterm t
nterm (IF t1 t2 t3) = IF <$> bterm' t1 <*> nterm t2 <*> nterm t3
nterm _ = Nothing


-- |
-- 数値
isNValue :: Term -> Bool
isNValue ZERO     = True
isNValue (SUCC n) = isNValue n
isNValue _        = False

-- |
-- ブール-数値
isBNValue :: Term -> Bool
isBNValue t = isBValue t || isNValue t

nrule :: Rule
nrule t = foldr1 (<|>) (map ($ t) [eSucc,ePredZero,ePredSucc,ePred,eIsZeroZero,eIsZeroSucc,eIsZero])

eSucc :: Rule
eSucc (SUCC t1) = let t1' = stepBN t1
                  in SUCC <$> t1'
eSucc _         = Nothing

ePredZero :: Rule
ePredZero t@ZERO = Just t
ePredZero _      = Nothing

ePredSucc :: Rule
ePredSucc (PRED (SUCC nv1)) = Just nv1
ePredSucc _                 = Nothing

ePred :: Rule
ePred (PRED t1) = let t1' = stepBN t1
                  in PRED <$> t1'
ePred _         = Nothing

eIsZeroZero :: Rule 
eIsZeroZero (IsZERO ZERO) = Just TRUE
eIsZeroZero _             = Nothing

eIsZeroSucc :: Rule
eIsZeroSucc (SUCC _) = Just FALSE
eIsZeroSucc _        = Nothing

eIsZero :: Rule
eIsZero (IsZERO t1) = let t1' = stepBN t1
                      in IsZERO <$> t1'
eIsZero _           = Nothing

stepN :: Term -> Maybe Term
stepN = nrule

stepBN :: Term -> Maybe Term
stepBN t = stepB t <|> stepN t

-- |
-- 数ではない正規形
isBadNValue :: Term -> Bool
isBadNValue WRONG = True
isBadNValue t     = isBValue t

-- |
-- ブール値ではない正規形
isBadBValue :: Term -> Bool
isBadBValue WRONG = True
isBadBValue t     = isNValue t

wrule :: Rule
wrule t =  foldr1 (<|>) (map ($ t) [eIfWrong,eSuccWrong,ePredWrong,eIsZeroWrong])

eIfWrong :: Rule
eIfWrong (IF t _ _) | isBadBValue t = Just WRONG
eIfWrong _                          = Nothing
       

eSuccWrong :: Rule
eSuccWrong (SUCC t) | isBadNValue t = Just WRONG
eSuccWrong _                        = Nothing

ePredWrong :: Rule
ePredWrong (PRED t) | isBadNValue t = Just WRONG
ePredWrong _                        = Nothing
                                      
eIsZeroWrong :: Rule
eIsZeroWrong (IsZERO t)  | isBadNValue t = Just WRONG
eIsZeroWrong _                           = Nothing

stepW :: Term -> Maybe Term
stepW = wrule

stepBNW :: Term -> Maybe Term
stepBNW t = stepBN t <|> stepW t

--

bValue :: Rule
bValue t | isBNValue t = Just t
         | otherwise   = Nothing
                         
bIfTrue :: Rule
bIfTrue (IF t1 t2 _) = eval t1 >>= \ v -> case v of
                         TRUE  -> eval t2
                         _     -> Nothing
bIfTrue _ = Nothing

bIfFalse :: Rule
bIfFalse (IF t1 _ t3) = eval t1 >>= \ v -> case v of
                          TRUE  -> eval t3
                          _     -> Nothing
bIfFalse _ = Nothing

bSucc :: Rule
bSucc (SUCC t1) = eval t1 >>= \ v -> if isNValue v then Just v else Nothing
bSucc _         = Nothing

bPredZero :: Rule
bPredZero (PRED t1) = eval t1 >>= \ v -> case v of
                      ZERO -> Just ZERO
                      _    -> Nothing
bPredZero _         = Nothing

bPredSucc :: Rule
bPredSucc (PRED t1) = eval t1 >>= \ v -> case v of
                      SUCC v' -> if isNValue v' then Just v' else Nothing
                      _       -> Nothing
bPredSucc _         = Nothing

bIsZeroZero :: Rule
bIsZeroZero (IsZERO t1) = eval t1 >>= \ v -> case v of
                          ZERO -> Just TRUE
                          _    -> Nothing
bIsZeroZero _ = Nothing

bIsZeroSucc :: Rule
bIsZeroSucc (IsZERO t1) = eval t1 >>= \ v -> case v of
                          SUCC v' -> if isNValue v' then Just FALSE else Nothing
                          _       -> Nothing
bIsZeroSucc _ = Nothing

erule :: Rule
erule t =  foldr1 (<|>) (map ($ t) [bValue,bIfTrue,bIfFalse,bSucc,bPredZero,bPredSucc,bIsZeroZero,bIsZeroSucc])

eval :: Term -> Maybe Term
eval = erule
