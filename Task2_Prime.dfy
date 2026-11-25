/*
 * CS F214: Logic in Computer Science
 * BITS Pilani, Hyderabad Campus
 * Assignment 2 - Task 2: Prime
 *
 * Method Specification:
 *   method Prime(val : int) returns (res : bool)
 *   requires val > 1
 *   ensures (res) <==> forall k :: 2 <= k < val ==> val % k != 0
 *
 * Description:
 *   Determines whether a strictly positive integer `val > 1` is prime by checking divisibility
 *   against all potential factors in the range [2, val).
 *   The loop maintains invariants to establish equivalence with the formal definition of primality.
 *   Total correctness is verified via the termination variant (decreases clause).
 */

method Prime(val : int) returns (res : bool)
  requires val > 1
  ensures (res) <==> forall k :: 2 <= k < val ==> val % k != 0
{
  var d := 2;
  while d < val
    // Invariant 1: Loop counter d remains within the valid search boundary.
    invariant 2 <= d <= val

    // Invariant 2: None of the integers in [2, d) divide val.
    invariant forall k :: 2 <= k < d ==> val % k != 0

    // Variant: Guarantees termination by strictly decreasing the remaining distance to val.
    decreases val - d
  {
    if val % d == 0 {
      // Counterexample found: d divides val, where 2 <= d < val.
      // Therefore, not all k in [2, val) satisfy val % k != 0.
      return false;
    }
    d := d + 1;
  }
  // When d == val, Invariant 2 matches the postcondition exactly.
  return true;
}

method Main() {
  print "=== Testing Task 2: Prime ===\n";

  var p2 := Prime(2);
  print "Prime(2) = ", p2, " (Expected: true)\n";
  expect p2 == true;

  var p3 := Prime(3);
  print "Prime(3) = ", p3, " (Expected: true)\n";
  expect p3 == true;

  var p4 := Prime(4);
  print "Prime(4) = ", p4, " (Expected: false)\n";
  expect p4 == false;

  var p17 := Prime(17);
  print "Prime(17) = ", p17, " (Expected: true)\n";
  expect p17 == true;

  var p25 := Prime(25);
  print "Prime(25) = ", p25, " (Expected: false)\n";
  expect p25 == false;

  print "Task 2 Tests Passed Successfully!\n\n";
}
