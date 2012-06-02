-- Graham scan algorithm for finding a convex hull in a finite set of points
-- http://en.wikipedia.org/wiki/Graham_scan
-- For alternative method, see:
-- http://www.algorithmist.com/index.php/Monotone_Chain_Convex_Hull
-- (sorts a set of points lexicographically)
-- CRLS has a very good exposition of Graham scan in Ch. 33.

module Main where

import Test.QuickCheck (quickCheck)
import Data.List ((\\), nub, sort, sortBy, minimumBy, union)

-- note that data constructors have to start with capital letters
data Direction = Left_ | Right_ | Straight_ deriving (Eq)
data Point2D = Point2D { x, y :: Double } deriving (Eq, Show)
type PointTuple = (Double, Double)

-- get direction of turn formed by three points going from p1 to p2 to p3
-- Do this by obtaining sign of the crossproduct of vectors (p1, p2) and
-- (p1, p3). If cross-product is positive, have left turn.
direction :: Point2D -> Point2D -> Point2D -> Direction
direction p1 p2 p3
    | cp > 0    = Left_
    | cp < 0    = Right_
    | otherwise = Straight_
    where cp       = (x2 - x1) * (y3 - y1) - (y2 - y1) * (x3 - x1)
          (x1, y1) = (x p1, y p1)
          (x2, y2) = (x p2, y p2)
          (x3, y3) = (x p3, y p3)

-- takes a list of 2D points and computes the direction of each successive
-- triple. Given a list of points [a,b,c,d,e], it should begin by computing the
-- turn made by [a,b,c], then the turn made by [b,c,d], then [c,d,e].
directions :: [Point2D] -> [Direction]
directions (p:q:r:ss) = direction p q r : directions (q:r:ss)
directions _ = []


-- get distance between two points p1 and p2
-- needed to find cosine (Graham scan)
distance :: Point2D -> Point2D -> Double
distance p1 p2 = sqrt ((x p2 - x p1) ^ 2 + (y p2 - y p1) ^ 2)

-- get cosine of two points with respect to X axis
cosX :: Point2D -> Point2D -> Double
cosX p1 p2 = (x p2 - x p1) / distance p1 p2

-- find the point with the lowest y-coordinate. If the lowest y-coordinate
-- exists in more than one point, choose point with the lowest x-coordinate
lowestYX :: Point2D -> Point2D -> Ordering
lowestYX p1 p2
    | y1 < y2   = LT
    | y1 > y2   = GT
    | otherwise = compare (x p1) (x p2)
    where y1 = y p1
          y2 = y p2

-- helper function to sort/pick points by their distance from pStart (larger is
-- better)
descCompareDist :: Point2D -> Point2D -> Point2D -> Ordering
descCompareDist pStart = compareDist
    where compareDist :: Point2D -> Point2D -> Ordering
          compareDist pA pB = compare distB distA
            where distA     = distanceP pA
                  distB     = distanceP pB
                  distanceP = distance pStart

-- helper function to sort/pick points by their cosine relative to pStart and to
-- the X axis (larger cosine is better)
descCompareCosX :: Point2D -> Point2D -> Point2D -> Ordering
descCompareCosX  pStart = compareCosX
    where compareCosX :: Point2D -> Point2D -> Ordering
          compareCosX pA pB
            | cosA > cosB = LT
            | cosA < cosB = GT
            | otherwise   = descCompareDist pStart pA pB
            where cosA  = cosXP pA
                  cosB  = cosXP pB
                  cosXP = cosX pStart

-- sorting using cosines here, but we could also sort using atan2() function
-- for example to find polar angle.
pivotSort :: [Point2D] -> [Point2D]
pivotSort xs =
    let p = minimumBy lowestYX xs
    in nub (p:sortBy (descCompareCosX p) xs)

-- This is the core of the algorithm
grahamScan :: [Point2D] -> [Point2D]
grahamScan []   = []
grahamScan [p] = [p]
grahamScan xs  =
    let (pStart:rStart:zs) = pivotSort xs
    in scanWith [rStart,pStart] zs
    where scanWith :: [Point2D] -> [Point2D] -> [Point2D]
          scanWith candidates@(q:r:rs) rest@(p:ps)
            -- Left turn: prepend element to candidates
            | myDir == Left_  = scanWith (p:candidates) ps
            -- Right turn: backtrack by one element
            | myDir == Right_ = scanWith (r:rs) rest
            -- Straight line: between q and r, choose the point that is furthest from p
            | otherwise = scanWith (furthest [p, q] :r:rs) ps
            where myDir    = direction r q p
                  furthest = minimumBy (descCompareDist r)
          scanWith done _  = done


-- convert tuple to Point2D
t2p :: PointTuple -> Point2D
t2p t = Point2D (fst t) (snd t)

-- convert Point2D to tuple
p2t :: Point2D -> PointTuple
p2t t = (x t, y t)

-- perform Graham Scan algorithm on tuples instead of on Point2D lists
grahamScanTuples :: [PointTuple] -> [PointTuple]
grahamScanTuples = map p2t . grahamScan . map t2p

-- {{{ For testing

-- pretty-print tuples
printTuples :: [PointTuple] -> String
printTuples ts = unlines (map (\t -> show (fst t) ++ "\t" ++ show (snd t)) ts)

-- Symmetric difference of sets (here represented as lists)
-- Written as: P ∆ Q (unicode u2206)
(-|-) :: Eq a => [a] -> [a] -> [a]
(-|-) p q = (p \\ q) `union` (q \\ p)

-- For use with QuickCheck: satisfy idempotence: a convex hull of a convex hull
-- must be the same set of points.
prop_isIdempotent :: [PointTuple] -> Bool
prop_isIdempotent xs = xsConv -|- xsConvConv == []
    where xsConv = grahamScanTuples xs
          xsConvConv = grahamScanTuples xsConv

-- For use with QuickCheck: satisfy the following property: for any valid input,
-- the output list must be a subset of the input list.
prop_isSubset :: [PointTuple] -> Bool
prop_isSubset xs = grahamScanTuples xs \\ xs == []

-- For use with QuickCheck: satisfy the following property: output must always
-- be the same no matter what order the points come in.
prop_orderIndependent :: [PointTuple] -> Bool
prop_orderIndependent xs = grahamScanTuples xs -|- grahamScanTuples (sort xs) == []

-- segments: given a list of points, return segments connecting the vertices in
-- the given order
segments :: [PointTuple] -> [(PointTuple, PointTuple)]
segments [] = []
segments xs = zip xs (tail xs ++ [head xs])

-- parea: find area of a polygon
parea :: [PointTuple] -> Double
parea []   = 0.0
parea [_] = 0.0
parea xs  = 0.5 * abs (sum [x0 * y1 - x1 * y0 | ((x0, y0), (x1, y1)) <- segments xs])

-- For use with QuickCheck: satisfy the following property: for any valid input,
-- the area of the convex hull of all points must be greater or equal than the
-- area of a convex hull of a subset of the points (in this case, we chose the
-- number of points in the subset to be equal to the number of points in the
-- original convex hull).
prop_areaIsGTE :: [PointTuple] -> Bool
prop_areaIsGTE xs =
    let xsConv = grahamScanTuples xs
    in parea xsConv >= parea (grahamScanTuples (take (length xsConv) xs))

-- A list of tuples where first elemtn is input, and second is expected output
testCases :: [([(Double,Double)],[(Double,Double)])]
testCases =
    [([],[]),

     ([(1,1)],
      [(1,1)]),

     ([(-1,0),(1,1)],
      [(-1,0),(1,1)]),

     ([(-1,0),(1,1),(2,3)],
      [(-1,0),(1,1),(2,3)]),

     ([(10,0), (10,1),(-10,1),(-10,0),(-7,0),(-10,2),(-10,3),(-4,1),(-2,2),(-12,1)],
      [(-12,1),(-10,3),(10,1),(10,0),(-10,0)]),

     ([(-3,7),(-2,6),(-1,4),(0,1),(0,0),(1,4),(2,6),(3,7)],
      [(-3,7),(3,7),(0,0)]),

     ([(-3,1),(-4,1),(-1,4),(0,0),(2,2),(-1,3),(-1,2),(1,0),(3,-1),(-1,-1)],
      [(-4,1),(-1,4),(2,2),(3,-1),(-1,-1)])]

-- OK/Fail plus string
type TestResult = (Bool, String)

-- Check our custom test cases
checkTestCases :: IO ()
checkTestCases = mapM_ doOneCase testCases
    where doOneCase myX = assertSameList (snd myX) (grahamScanTuples (fst myX))
          assertSameList expected actual
            | sort expected == sort actual = putStrLn "Passed"
            | otherwise                   =
                putStrLn ("Failed. Expected:\n" ++ printTuples expected ++ "\nActual:\n" ++ printTuples actual)

-- another property that a scan must satisfy is that the output must remain the
-- same regardless of which order the points are in. TODO: write a test that
-- takes an input list of points and compares the output from the list in an
-- unsorted form with the output from the list in sorted form.
runTests :: IO ()
runTests = do checkTestCases
              quickCheck prop_isIdempotent
              quickCheck prop_isSubset
              quickCheck prop_areaIsGTE
              quickCheck prop_orderIndependent

-- }}}
