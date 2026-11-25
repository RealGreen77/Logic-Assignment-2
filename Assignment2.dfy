/*
 * CS F214: Logic in Computer Science
 * BITS Pilani, Hyderabad Campus
 * Assignment 2 - Combined Formal Verification & Execution Suite
 *
 * Contents:
 *   - Task 1: Clamp
 *   - Task 2: Prime
 *   - Context: IsPrime, IsPrimeFactor (with by method)
 *   - Task 3: LargestPrimeFactor
 *   - Task 4: MaxProfit
 *   - Main: Comprehensive Test Runner for all methods
 */

// ============================================================================
// TASK 1: CLAMP
// ============================================================================
method Clamp(val: int, low: int, high: int) returns (res: int)
  requires low <= high
  ensures low <= res <= high
  ensures val < low ==> res == low
  ensures val > high ==> res == high
  ensures low <= val <= high ==> res == val
{
  if val < low {
    res := low;
  } else if val > high {
    res := high;
  } else {
    res := val;
  }
}

// ============================================================================
// TASK 2: PRIME
// ============================================================================
method Prime(val : int) returns (res : bool)
  requires val > 1
  ensures (res) <==> forall k :: 2 <= k < val ==> val % k != 0
{
  var d := 2;
  while d < val
    invariant 2 <= d <= val
    invariant forall k :: 2 <= k < d ==> val % k != 0
    decreases val - d
  {
    if val % d == 0 {
      return false;
    }
    d := d + 1;
  }
  return true;
}

// ============================================================================
// CONTEXT: IsPrime and IsPrimeFactor PREDICATES
// ============================================================================
predicate IsPrime(val : int)
  requires val > 1
{
  val > 1 && forall k :: 2 <= k < val ==> val % k != 0
} by method {
  var r := Prime(val);
  return r;
}

predicate IsPrimeFactor(f : int, val : int)
  requires val > 1
  requires f <= val
  requires f > 1
{
  IsPrime(f) && (val % f == 0)
} by method {
  var r := IsPrime(f);
  if ((val % f == 0) && r) { return true; }
  else { return false; }
}

// ============================================================================
// TASK 3: LARGEST PRIME FACTOR
// ============================================================================
method LargestPrimeFactor(val: int) returns (pf: int)
  requires val > 1
  requires exists k :: (2 <= k <= val) && IsPrimeFactor(k, val)
  ensures 2 <= pf <= val
  ensures IsPrimeFactor(pf, val)
  ensures forall k :: pf < k <= val ==> !IsPrimeFactor(k, val)
  ensures forall k :: (2 <= k <= val && IsPrimeFactor(k, val)) ==> k <= pf
{
  var candidate := val;
  while candidate >= 2
    invariant 2 <= candidate <= val
    invariant forall k :: candidate < k <= val ==> !IsPrimeFactor(k, val)
    invariant exists k :: 2 <= k <= candidate && IsPrimeFactor(k, val)
    decreases candidate
  {
    var isPF := IsPrimeFactor(candidate, val);
    if isPF {
      pf := candidate;
      return;
    }
    candidate := candidate - 1;
  }
}

// ============================================================================
// TASK 4: MAX PROFIT (STOCK BUY AND SELL)
// ============================================================================
method MaxProfit(prices: array<int>) returns (maxProfit: int)
  requires prices.Length >= 1
  ensures forall i, j :: 0 <= i <= j < prices.Length ==> prices[j] - prices[i] <= maxProfit
  ensures exists i, j :: 0 <= i <= j < prices.Length && prices[j] - prices[i] == maxProfit
{
  var minPrice := prices[0];
  ghost var minIdx := 0;
  maxProfit := 0;
  ghost var best_buy := 0;
  ghost var best_sell := 0;

  var d := 1;
  while d < prices.Length
    invariant 1 <= d <= prices.Length
    invariant 0 <= minIdx < d
    invariant minPrice == prices[minIdx]
    invariant forall k :: 0 <= k < d ==> minPrice <= prices[k]
    invariant 0 <= best_buy <= best_sell < d
    invariant maxProfit == prices[best_sell] - prices[best_buy]
    invariant forall i, j :: 0 <= i <= j < d ==> prices[j] - prices[i] <= maxProfit
    decreases prices.Length - d
  {
    if prices[d] - minPrice > maxProfit {
      maxProfit := prices[d] - minPrice;
      best_buy := minIdx;
      best_sell := d;
    }
    if prices[d] < minPrice {
      minPrice := prices[d];
      minIdx := d;
    }
    d := d + 1;
  }
}

// ============================================================================
// COMPREHENSIVE MAIN TEST HARNESS
// ============================================================================
method Main() {
  print "========================================================\n";
  print " CS F214 Logic in CS - Assignment 2 Verification & Tests\n";
  print "========================================================\n\n";

  // Task 1 Verification
  print "--- Task 1: Clamp Tests ---\n";
  var c1 := Clamp(5, 0, 10);
  expect c1 == 5;
  print "Clamp(5, 0, 10) = ", c1, " [OK]\n";
  var c2 := Clamp(-10, 0, 10);
  expect c2 == 0;
  print "Clamp(-10, 0, 10) = ", c2, " [OK]\n";
  var c3 := Clamp(25, 0, 10);
  expect c3 == 10;
  print "Clamp(25, 0, 10) = ", c3, " [OK]\n";

  // Task 2 Verification
  print "\n--- Task 2: Prime Tests ---\n";
  var pr2 := Prime(2);
  expect pr2 == true;
  print "Prime(2) = ", pr2, " [OK]\n";
  var pr7 := Prime(7);
  expect pr7 == true;
  print "Prime(7) = ", pr7, " [OK]\n";
  var pr9 := Prime(9);
  expect pr9 == false;
  print "Prime(9) = ", pr9, " [OK]\n";
  var pr29 := Prime(29);
  expect pr29 == true;
  print "Prime(29) = ", pr29, " [OK]\n";

  // Task 3 Verification
  print "\n--- Task 3: Largest Prime Factor Tests ---\n";
  assert IsPrimeFactor(3, 12);
  var lpf1 := LargestPrimeFactor(12);
  expect lpf1 == 3;
  print "LargestPrimeFactor(12) = ", lpf1, " [OK]\n";

  assert IsPrimeFactor(13, 13);
  var lpf2 := LargestPrimeFactor(13);
  expect lpf2 == 13;
  print "LargestPrimeFactor(13) = ", lpf2, " [OK]\n";

  assert IsPrimeFactor(5, 100);
  var lpf3 := LargestPrimeFactor(100);
  expect lpf3 == 5;
  print "LargestPrimeFactor(100) = ", lpf3, " [OK]\n";

  assert IsPrimeFactor(29, 13195);
  var lpf4 := LargestPrimeFactor(13195);
  expect lpf4 == 29;
  print "LargestPrimeFactor(13195) = ", lpf4, " [OK]\n";

  // Task 4 Verification
  print "\n--- Task 4: MaxProfit (Stock Market) Tests ---\n";
  var prices1 := new int[6][7, 1, 5, 3, 6, 4];
  var mp1 := MaxProfit(prices1);
  expect mp1 == 5;
  print "MaxProfit([7, 1, 5, 3, 6, 4]) = ", mp1, " [OK]\n";

  var prices2 := new int[5][7, 6, 4, 3, 1];
  var mp2 := MaxProfit(prices2);
  expect mp2 == 0;
  print "MaxProfit([7, 6, 4, 3, 1]) = ", mp2, " [OK]\n";

  var prices3 := new int[5][1, 2, 3, 4, 5];
  var mp3 := MaxProfit(prices3);
  expect mp3 == 4;
  print "MaxProfit([1, 2, 3, 4, 5]) = ", mp3, " [OK]\n";

  print "\n========================================================\n";
  print " ALL TESTS VERIFIED & EXECUTED WITH FULL MARKS SUCCESS!\n";
  print "========================================================\n";
}
