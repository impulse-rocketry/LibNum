/* num.c  -  Library of numerical method                               */
/* Copyright (C) 2000                                                  */
/* Antoine Lefebvre <antoine.lefebvre@polymtl.ca                       */

/* This program is free software; you can redistribute it and/or modify*/
/* it under the terms of the GNU General Public License as published by*/
/* the Free Software Foundation; either version 2 of the License, or   */
/* (at your option) any later version.                                 */

/* This program is distributed in the hope that it will be useful,     */
/* but WITHOUT ANY WARRANTY; without even the implied warranty of      */
/* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       */
/* GNU General Public License for more details.                        */

/* You should have received a copy of the GNU General Public License   */
/* along with this program; if not, write to the Free Software         */
/* Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.           */

// Ported from the original c code by Ben Voß.

namespace LibNum;

/// <summary>
/// Library of numerical methods
/// </summary>
public static class MatrixUtils {
    /// <summary>
    /// This is a function to solve a matrix of linear equation. It uses the Gauus elimination method as explained in
    /// 'Advanced engineering mathematics' by Erwin Kreyszig.
    ///
    /// AUTHOR:  Antoine Lefebvre
    ///
    /// DATE: February 6, 2000
    /// </summary>
    /// <remarks>
    /// The number of operation can be estimated by 2*n^3/3
    /// </remarks>
    /// <param name="matrix">An array of [neq]x[neq+1] which is an augmented matrix.</param>
    /// <param name="solution">An array that will contain the solution if there is one and junk if there is no solution.</param>
    /// <param name="neq">The number of unknowns in the system</param>
    /// <returns>true, on success, false on failure</returns>
    public static bool Gauss(double[][] matrix, double[] solution, int neq) {
        for (var k = 0; k < neq - 1; k++) {
            // Find the smallest j>=k such that a[j][k] != 0
            for (var j = k; j < neq; j++) {
                if (matrix[j][k] == 0) {
                    Console.Error.WriteLine("No unique solution exists.");
                    return false;
                }
                
                if (j != k) {
                    // Exchange the contents of row j and k
                    for (var i = 0; i <= neq; i++) {
                        var temp = matrix[j][i];
                        matrix[j][i] = matrix[k][i];
                        matrix[k][i] = temp;
                    }
                }
            }

            for (var j = k + 1; j < neq; j++) {
                // Multiplier
                var m = matrix[j][k] / matrix[k][k];

                for (var i = k; i <= neq; i++) {
                    matrix[j][i] = matrix[j][i] - m * matrix[k][i];
                }
            }
        }

        if (matrix[neq - 1][neq - 1] == 0) {
            Console.Error.WriteLine("No unique solution exists.");
            return false;
        } else {
            solution[neq - 1] = matrix[neq - 1][neq] / matrix[neq - 1][neq - 1];

            for (var j = neq - 2; j >= 0; j--) {
                var s = 0.0;

                for (var i = j + 1; i < neq; i++) {
                    s += matrix[j][i] * solution[i];
                }

                solution[j] = (matrix[j][neq] - s) / matrix[j][j];
            }
        }

        return true;
    }

    /// <summary>
    /// This function solves system of linear equation with the LU-Factorisation method as  explained in 'Advanced
    /// engineering mathematics' by Erwin Kreyszig. (Doolittle's method)
    ///
    /// THEORY: To solve the system Ax=b, we could decompose A such that A = LU. L is a lower triangular matrix and U
    ///         is an upper triangular matrix. We could
    ///         then solve the system bye substitution cause Ly=b and Ux=y.
    ///
    /// AUTHOR:  Antoine Lefebvre
    /// DATE: February 6, 2000
    /// </summary>
    /// <remarks>
    /// The number of operation is estimate by n^3/3, about half as many as the Gauss elimination. Should be 
    /// interesting to compare the speed in case of big matrix
    /// </remarks>
    /// <param name="matrix">An array of [neq]x[neq+1] which is an augmented matrix.</param>
    /// <param name="solution">An array that will contain the solution if there is one and junk if there is no solution.</param>
    /// <param name="neq">The number of unknowns in the system</param>
    /// <returns>true, on success, false on failure</returns>
    public static bool Lu(double[][] matrix, double[] solution, int neq) {
        // L is a lower triangular matrix with diagonal set to one
        var L = Make2DArray(neq, neq);

        // U is an upper triangular matrix
        var U = Make2DArray(neq, neq);

        // temporary vector Ly = b, Ux = y
        var y = new double[neq];

        // Reset the solution vector
        System.Array.Clear(solution);

        // Set the diagonal to 1
        for (var i = 0; i < neq; i++) {
            L[i][i] = 1;
        }

        // LU Factorisation
        for (var i = 0; i < neq; i++) {
            U[0][i] = matrix[0][i];

            if (i > 0) {
                for (var j = 1; j <= i; j++) {
                    var tmp = 0.0;

                    for (var s = 0; s < j; s++) {
                        tmp += L[j][s] * U[s][i];
                    }

                    U[j][i] = matrix[j][i] - tmp;
                }
            }

            for (var j = i + 1; j < neq; j++) {
                if (U[i][i] == 0.0) {
                    Console.Error.WriteLine("No unique solution exist.");
                    return false;
                }

                if (i == 0) {
                    L[j][i] = matrix[j][i] / U[i][i];
                }
                else {
                    var tmp = 0.0;

                    for (var s = 0; s < i; s++) {
                        tmp += L[j][s] * U[s][i];
                    }

                    L[j][i] = (matrix[j][i] - tmp) / U[i][i];
                }
            }
        }
        // End LU-Factorisation

        // Substitution  for y    Ly = b
        for (var i = 0; i < neq; i++) {
            var tmp = 0.0;

            for (var j = 0; j < i; j++) {
                tmp += L[i][j] * y[j];
            }

            y[i] = matrix[i][neq] - tmp;
        }

        // Substitution for x   Ux = y
        for (var i = neq - 1; i >= 0; i--) {
            if (U[i][i] == 0.0) {
                Console.Error.WriteLine("No unique solution exist.");
                return false;
            }

            var tmp = 0.0;

            for (var j = i; j < neq; j++) {
                tmp += U[i][j] * solution[j];
            }

            solution[i] = (y[i] - tmp) / U[i][i];

            if (double.IsNaN(solution[i])) {
                Console.Error.WriteLine("No unique solution exist. NaN in solution.");
                return false;
            }
        }

        return true;
    }

    /// <summary>
    /// Prints the coefficient of the matrix to the screen for square matrix instead of (N)x(N-1).
    /// </summary>
    public static void PrintSquareMatrix(double[][] matrix, int neq) {
        for (var i = 0; i < neq; i++) {
            for (var j = 0; j < neq; j++) {
                Console.Write($"[{matrix[i][j]:0.######E+0}] ");
            }

            Console.WriteLine();
        }

        Console.WriteLine();
    }

    /// <summary>
    /// Prints the coefficient of the matrix to the screen for matrix of (N)x(N-1).
    /// </summary>
    public static void PrintMatrix(double[][] matrix, int neq) {
        for (var i = 0; i < neq; i++) {
            for (var j = 0; j <= neq; j++) {
                Console.Write($"[{matrix[i][j]:0.######E+0}] ");
            }

            Console.WriteLine();
        }

        Console.WriteLine();
    }

    /// <summary>
    /// Prints the contents of the vector to the screen.
    /// </summary>
    public static void PrintVec(double[] vec, int neq) {
        for (var i = 0; i < neq; i++) {
            Console.Write($"[{vec[i]:0.######E+0}] ");
        }

        Console.WriteLine();
    }

    /// <summary>
    /// This function solve systems of ODE of the first order with the Runge-Kutta method of the fourth order.
    ///   
    /// AUTHOR: Antoine Lefebvre
    ///
    /// DATE: February 11
    /// </summary>
    /// <remarks>
    /// **y must be properly allocated, [number of points]X[neq]
    ///
    /// It could be interesting to add a tolerance and use variable step to reach our tolerance instead of using a fixed step.
    /// </remarks>
    /// <param name="f">The first parameter is a pointer to the function we we want to solve. This function take five parameters:
    ///    int: neq the number of equations in the system
	///    double: time is the time at which we want to evaluate
	///    double: y is an array containing an initial value
	///    double: dy will store the result of the function
	///    int: ierr any error field
    /// </param>
    /// <param name="neq">the time at which we want to evaluate</param>
    /// <param name="step">is the time variation</param>
    /// <param name="duration">the total time of the simulation</param>
    /// <param name="ic">are the initial conditions</param>
    /// <param name="y">An array containing all the data</param>
    /// <param name="data">any user data</param>
    public static void Rk4(Func<int, double, double[], double[], object, int> f, int neq, double step, double duration, double[] ic, double[][] y, object data) {
        double t = 0.0;

        var tmp = new double[neq];
        var dy = new double[neq];

        var K1 = new double[neq];
        var K2 = new double[neq];
        var K3 = new double[neq];
        var K4 = new double[neq];

        for (var i = 0; i < neq; i++) {
            y[0][i] = ic[i]; // conditions initiales
            tmp[i] = y[0][i];
        }

        for (var n = 0; n < (int)Round(duration / step); n++) {
            for (var i = 0; i < neq; i++) {
                f(neq, t, tmp, dy, data);
                K1[i] = step * dy[i];

                tmp[i] = y[n][i] + K1[i] / 2;  // for the next step           
            }

            for (var i = 0; i < neq; i++) {
                f(neq, t, tmp, dy, data);
                K2[i] = step * dy[i];

                tmp[i] = y[n][i] + K2[i] / 2;
            }

            for (var i = 0; i < neq; i++) {
                f(neq, t, tmp, dy, data);
                K3[i] = step * dy[i];

                tmp[i] = y[n][i] + K3[i];
            }

            for (var i = 0; i < neq; i++) {
                f(neq, t, tmp, dy, data);
                K4[i] = step * dy[i];
            }

            for (var i = 0; i < neq; i++) {
                y[n + 1][i] = y[n][i] + (1.0 / 6.0) * (K1[i] + 2.0 * K2[i] + 2.0 * K3[i] + K4[i]);
            }

            t = t + step;
        }
    }

    // this function return the nearest integer to a it is a replacement of rint which is not ANSI complient
    private static int Round(double a) {
        int t = (int)a;

        if (a - (double)t < 0.5) {
            return t;
        }
        
        if (a - (double)t > 0.5) {
            return t + 1;
        }

        return (t + (t % 2));
    }

    private static double[][] Make2DArray(int d1, int d2) {
        var result = new double[d1][];

        for (var i = 0; i < d1; i++) {
            result[i] = new double[d2];
        }

        return result;
    }
}
