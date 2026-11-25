/*
 * CS F214: Logic in Computer Science
 * BITS Pilani, Hyderabad Campus
 * Assignment 2 - Task 4: MaxProfit (Stock Buy and Sell)
 *
 * Method Specification:
 *   method MaxProfit(prices: array<int>) returns (maxProfit: int)
 *   requires prices.Length >= 1
 *   ensures forall i, j :: 0 <= i <= j < prices.Length ==> prices[j] - prices[i] <= maxProfit
 *   ensures exists i, j :: 0 <= i <= j < prices.Length && prices[j] - prices[i] == maxProfit
 *
 * Description:
 *   Solves the single transaction buy-and-sell problem in O(N) linear time and O(1) auxiliary space.
 *   Proves two fundamental properties:
 *   1. Optimality: No valid pair of days (i, j) with 0 <= i <= j < prices.Length yields profit > maxProfit.
 *   2. Achievability: There exists a concrete witness pair of days (i, j) yielding exactly maxProfit.
 *   Ghost variables track the witness pair and minimum price index with zero runtime cost.
 */

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
    // Invariant 1: Loop index d is within valid range [1, prices.Length]
    invariant 1 <= d <= prices.Length

    // Invariant 2: minIdx is a valid index in [0, d) and correctly points to minPrice
    invariant 0 <= minIdx < d
    invariant minPrice == prices[minIdx]

    // Invariant 3: minPrice is indeed the minimum element in prices[0..d)
    invariant forall k :: 0 <= k < d ==> minPrice <= prices[k]

    // Invariant 4: Witness pair (best_buy, best_sell) is valid within [0, d)
    invariant 0 <= best_buy <= best_sell < d

    // Invariant 5: Achievability witness: maxProfit is exactly the profit of the witness pair
    invariant maxProfit == prices[best_sell] - prices[best_buy]

    // Invariant 6: Optimality: maxProfit is >= any profit achievable from pairs in [0, d)
    invariant forall i, j :: 0 <= i <= j < d ==> prices[j] - prices[i] <= maxProfit

    // Variant: Decreasing remaining days, guaranteeing termination
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

method Main() {
  print "=== Testing Task 4: MaxProfit ===\n";

  // Test Case 1: Standard LeetCode example [7, 1, 5, 3, 6, 4] -> Buy day 1 (price 1), Sell day 4 (price 6), profit = 5
  var a1 := new int[6][7, 1, 5, 3, 6, 4];
  var p1 := MaxProfit(a1);
  print "MaxProfit([7, 1, 5, 3, 6, 4]) = ", p1, " (Expected: 5)\n";
  expect p1 == 5;

  // Test Case 2: Monotonically decreasing prices [7, 6, 4, 3, 1] -> Buy and sell same day, profit = 0
  var a2 := new int[5][7, 6, 4, 3, 1];
  var p2 := MaxProfit(a2);
  print "MaxProfit([7, 6, 4, 3, 1]) = ", p2, " (Expected: 0)\n";
  expect p2 == 0;

  // Test Case 3: Single day [10] -> Buy and sell day 0, profit = 0
  var a3 := new int[1][10];
  var p3 := MaxProfit(a3);
  print "MaxProfit([10]) = ", p3, " (Expected: 0)\n";
  expect p3 == 0;

  // Test Case 4: Monotonically increasing prices [1, 2, 4, 7, 11] -> Buy day 0 (price 1), Sell day 4 (price 11), profit = 10
  var a4 := new int[5][1, 2, 4, 7, 11];
  var p4 := MaxProfit(a4);
  print "MaxProfit([1, 2, 4, 7, 11]) = ", p4, " (Expected: 10)\n";
  expect p4 == 10;

  print "Task 4 Tests Passed Successfully!\n\n";
}
