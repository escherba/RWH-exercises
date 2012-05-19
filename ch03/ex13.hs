-- Graham scan algorithm:
-- Find a convex hull in a finite set of points
-- http://en.wikipedia.org/wiki/Graham_scan
-- For alternative method, see:
-- http://www.algorithmist.com/index.php/Monotone_Chain_Convex_Hull
-- sort a set of points lexicographically, first by x-coordinate, 
-- and in case of a tie, by y-coordinate
-- Also an a fast method described in CRLS.

import Data.List (sortBy, nub, minimumBy)

-- note that data constructors have to start with capital letters
data Direction = Left_ | Right_ | Straight_ deriving (Eq, Show)

data Point2D = Point2D {
    x :: Double,
    y :: Double
} deriving (Eq, Show)

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
directions (p:q:r:ss) = (direction p q r) : (directions (q:r:ss))
directions _ = []


-- get distance between two points p1 and p2
-- needed to find cosine (Graham scan)
distance :: Point2D -> Point2D -> Double
distance p1 p2 = sqrt ((x p2 - x p1) ^ 2 + (y p2 - y p1) ^ 2)

-- get cosine of two points with respect to X axis
cosX :: Point2D -> Point2D -> Double
cosX p1 p2 = (x p2 - x p1) / (distance p1 p2)

-- find the point with the lowest y-coordinate. If the lowest y-coordinate
-- exists in more than one point, choose point with the lowest x-coordinate
lowestYX :: Point2D -> Point2D -> Ordering
lowestYX p1 p2
    | y1 < y2   = LT
    | y1 > y2   = GT
    | otherwise = compare (x p1) (x p2)
    where y1 = y p1
          y2 = y p2

-- call the point with the lowest coordinate P
findP :: [Point2D] -> Point2D
findP ps = minimumBy lowestYX ps

-- helper function to sort/pick points by their distance from pStart (larger is
-- better)
descCompareDist :: Point2D -> (Point2D -> Point2D -> Ordering)
descCompareDist pStart = compareDist
    where compareDist :: Point2D -> Point2D -> Ordering
          compareDist pA pB
            | distA > distB = LT
            | distA < distB = GT
            | otherwise     = EQ
            where distA     = distanceP pA
                  distB     = distanceP pB
                  distanceP = distance pStart

-- helper function to sort/pick points by their cosine relative to pStart and to
-- the X axis (larger cosine is better)
descCompareCosX :: Point2D -> (Point2D -> Point2D -> Ordering)
descCompareCosX  pStart = compareCosX
    where compareCosX :: Point2D -> Point2D -> Ordering
          compareCosX pA pB
            | cosA > cosB = LT
            | cosA < cosB = GT
            | otherwise   = (descCompareDist pStart) pA pB
            where cosA  = cosXP pA
                  cosB  = cosXP pB
                  cosXP = cosX pStart

-- sorting using cosines here, but we could also sort using atan2() function
--  for example to find polar angle.
myPivotSort xs = pStart:(sortBy (descCompareCosX pStart) cleanInput)
    where uniqueList = nub xs
          pStart     = findP uniqueList
          cleanInput = [x | x <- uniqueList, x /= pStart]

-- This is the core of the algorithm
grahamScan :: [Point2D] -> [Point2D]
grahamScan []     = []
grahamScan [p]    = [p]
grahamScan xs = 
    let (x:y:zs) = myPivotSort xs
    in myGrahamScan [y,x] zs
    where myGrahamScan :: [Point2D] -> [Point2D] -> [Point2D]
          myGrahamScan (q:r:rs) (p:ps)
            | myDir == Left_  = myGrahamScan (p:q:r:rs) ps
            -- backtrack by one element
            | myDir == Right_ = myGrahamScan (r:rs) (p:ps)
            -- between q and r, choose the point that is furthest from p
            | otherwise = myGrahamScan ((furthest [p, q]):r:rs) ps
            where myDir    = direction r q p
                  furthest = minimumBy (descCompareDist r)
          myGrahamScan done _  = done


-- convert tuple to Point2D
t2p :: [(Double, Double)] -> [Point2D]
t2p [] = []
t2p (t:ts) = (Point2D (fst t) (snd t)) : (t2p ts)

-- convert Point2D to tuple
p2t :: [Point2D] -> [(Double, Double)]
p2t [] = []
p2t (t:ts) = (x t, y t) : (p2t ts)

-- pretty-print tuples
printTuples [] = ""
printTuples (t:ts) = (show (fst t)) ++ "\t" ++ (show (snd t)) ++ "\n" ++ (printTuples ts)


-- TEST CASES -------------------------------------------
testCase1 = t2p [(10,0), (10,1),(-10,1),(-10,0),(-7,0),(-10,2),(-10,3),(-4,1),(-2,2),(-12,1)]
-- expected answer: [(-12,1),(-10,3),(10,1),(10,0),(-10,0)]

testCase2 = t2p [(-3,7),(-2,6),(-1,4),(0,1),(0,0),(1,4),(2,6),(3,7)]
-- expected answer: [(-3,7),(3,7),(0,0)]

testCase3 = t2p [(-3,1),(-4,1),(-1,4),(0,0),(2,2),(-1,3),(-1,2),(1,0),(3,-1),(-1,-1)]
-- expected answer: [(-4,1),(-1,4),(2,2),(3,-1),(-1,-1)]