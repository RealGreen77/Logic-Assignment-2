/*
 * CS F214: Logic in Computer Science
 * BITS Pilani, Hyderabad Campus
 * Assignment 2 - Task 1: Clamp
 *
 * Method Specification:
 *   method Clamp(val: int, low: int, high: int) returns (res: int)
 *
 * Description:
 *   Clamps an input integer `val` between a lower bound `low` and upper bound `high`.
 *   - If val < low, the result is low.
 *   - If val > high, the result is high.
 *   - If low <= val <= high, the result is val.
 */

method Clamp(val: int, low: int, high: int) returns (res: int)
  // Precondition: For clamping to be mathematically valid, low must not exceed high.
  requires low <= high

  // Postcondition 1: The returned value is guaranteed to be within [low, high].
  ensures low <= res <= high

  // Postconditions 2-4: Exact functional equivalence defining clamping behavior.
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

method Main() {
  print "=== Testing Task 1: Clamp ===\n";
  
  var r1 := Clamp(5, 0, 10);
  print "Clamp(5, 0, 10) = ", r1, " (Expected: 5)\n";
  assert r1 == 5;

  var r2 := Clamp(-3, 0, 10);
  print "Clamp(-3, 0, 10) = ", r2, " (Expected: 0)\n";
  assert r2 == 0;

  var r3 := Clamp(15, 0, 10);
  print "Clamp(15, 0, 10) = ", r3, " (Expected: 10)\n";
  assert r3 == 10;

  var r4 := Clamp(7, 7, 7);
  print "Clamp(7, 7, 7) = ", r4, " (Expected: 7)\n";
  assert r4 == 7;

  print "Task 1 Tests Passed Successfully!\n\n";
}
