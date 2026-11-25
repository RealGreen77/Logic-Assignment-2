/*
 * CS F214: Logic in Computer Science
 * BITS Pilani, Hyderabad Campus
 * Assignment 2 - Task 3: Largest Prime Factor
 *
 * Method Specification:
 *   method LargestPrimeFactor(val: int) returns (pf: int)
 *   requires val > 1
 *   requires exists k :: (2 <= k <= val) && IsPrimeFactor(k, val)
 *
 * Description:
 *   Finds the greatest prime factor of a given integer `val > 1`.
 *   Uses context predicates `IsPrime` and `IsPrimeFactor` defined with `by method`.
 *   Proves both partial correctness (pf is a prime factor and greater than or equal
 *   to any other prime factor) and total correctness (loop termination guaranteed).
 */

// Method Prime from Task 2 (needed for the executable body of IsPrime)
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

// Context: Predicate IsPrime with logical spec and executable body
predicate IsPrime(val : int)
  requires val > 1
{
  val > 1 && forall k :: 2 <= k < val ==> val % k != 0
} by method {
  var r := Prime(val);
  return r;
}

// Context: Predicate IsPrimeFactor with logical spec and executable body
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

// Task 3: LargestPrimeFactor Method
method LargestPrimeFactor(val: int) returns (pf: int)
  requires val > 1
  requires exists k :: (2 <= k <= val) && IsPrimeFactor(k, val)

  // Postcondition 1: Returned factor is within the valid range [2, val]
  ensures 2 <= pf <= val

  // Postcondition 2: Returned value is indeed a prime factor of val
  ensures IsPrimeFactor(pf, val)

  // Postcondition 3: No prime factor exists strictly above pf (Rigorous Maximality)
  ensures forall k :: pf < k <= val ==> !IsPrimeFactor(k, val)

  // Postcondition 4: Any prime factor of val is <= pf (Equivalence Formulation)
  ensures forall k :: (2 <= k <= val && IsPrimeFactor(k, val)) ==> k <= pf
{
  var candidate := val;
  while candidate >= 2
    // Invariant 1: Candidate is bounded between 2 and val
    invariant 2 <= candidate <= val

    // Invariant 2: No integer strictly greater than candidate is a prime factor
    invariant forall k :: candidate < k <= val ==> !IsPrimeFactor(k, val)

    // Invariant 3: The existence of a prime factor is maintained within [2, candidate]
    invariant exists k :: 2 <= k <= candidate && IsPrimeFactor(k, val)

    // Variant: Decreases candidate towards 2, proving termination
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

method Main() {
  print "=== Testing Task 3: Largest Prime Factor ===\n";

  // 12 = 2^2 * 3 -> LPF is 3
  assert IsPrimeFactor(3, 12);
  var p1 := LargestPrimeFactor(12);
  print "LargestPrimeFactor(12) = ", p1, " (Expected: 3)\n";
  expect p1 == 3;

  // 13 is prime -> LPF is 13
  assert IsPrimeFactor(13, 13);
  var p2 := LargestPrimeFactor(13);
  print "LargestPrimeFactor(13) = ", p2, " (Expected: 13)\n";
  expect p2 == 13;

  // 100 = 2^2 * 5^2 -> LPF is 5
  assert IsPrimeFactor(5, 100);
  var p3 := LargestPrimeFactor(100);
  print "LargestPrimeFactor(100) = ", p3, " (Expected: 5)\n";
  expect p3 == 5;

  // 13195 = 5 * 7 * 13 * 29 -> LPF is 29
  assert IsPrimeFactor(29, 13195);
  var p4 := LargestPrimeFactor(13195);
  print "LargestPrimeFactor(13195) = ", p4, " (Expected: 29)\n";
  expect p4 == 29;

  print "Task 3 Tests Passed Successfully!\n\n";
}
