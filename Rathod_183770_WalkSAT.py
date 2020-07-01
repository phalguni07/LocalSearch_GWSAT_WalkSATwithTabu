import operator
import sys
import random as rand
import time
from collections import Counter
from copy import deepcopy, copy
from random import random, choice
import matplotlib.pyplot as plt

# -----------------------#
# Author: Phalguni Rathod
# Student Id: R00183770
# -----------------------#

# sat_sol() & readFromFile() are taken from Dr. Grimes solution for lab - Sat Checker, with some modification to make the
# code suitable for my usage. And Hence, I changed the names.
def sat_sol(clauses, data_sol):
    """
    Modified version of Dr. Grimes Sat Checker
    :param clauses: Takes the 2D-List of clauses
    :param data_sol: List of Solution
    :return: True/False: If Given Solution fits all the given clauses
             Unsat_List: List of Unsatisfied clauses
             Sat_List:  List of Unsatisfied clauses
    """

    def readSolution(data):
        """
        Reads data in list form & returns dictionary of variables & literals
        :param data: List of Solution
        :return: Dictionary of Variables & literals
        """

        vars = {}  # Dictionary definition
        for literal in data:  # Taking each variable from data(list)
            literal = int(literal)  # Converting into integer
            var = literal  # Storing into var for further modification
            if var < 0:  # If var is negative
                vars[-var] = 0  # Assign Zero (or we could have done False, but didn't do that)
            else:
                vars[var] = 1  # Assign One (or we could have done True, but didn't do that)
        return vars  # Return the dictionary

    def solutionStatus(instance, sol):
        """
        Modified version of Dr. Grimes Sat Checker
        This function checks if given solution is valid for given instances/clauses
        :param instance: List of all clauses
        :param sol: List of literals
        :return: True/False: If Given Solution fits all the given clauses
             Unsat_List: List of Unsatisfied clauses
             Sat_List:  List of Unsatisfied clauses
        """
        sat_sol = []
        unsat_sol = []

        clause = instance
        unsat_clause = 0
        for clause_i in clause:
            cStatus = False
            tmp = []
            for var in clause_i:
                if var < 0:
                    if (1 - sol[-var]) == 1:
                        cStatus = True
                    tmp.append([var, sol[-var]])
                else:
                    tmp.append([var, sol[var]])
                    if sol[var] == 1:
                        cStatus = True
            if not cStatus:
                unsat_sol.append(clause_i)
                unsat_clause += 1
            else:
                sat_sol.append(clause_i)

        if unsat_clause > 0:
            return [False, unsat_sol, sat_sol]
        return [True, unsat_sol, sat_sol]

    solution = readSolution(data_sol)
    output = solutionStatus(clauses, solution)

    return output


def readFromFile(fName):
    """
    Modified version of Dr. Grimes Sat Checker

    :param fName: File to be read to get clauses
    :return: Variables used in all the clauses
             Clauses: 2D List of clauses read from file
    """
    file        = open(fName, 'r')
    tVariables  = -1
    tClauses    = -1
    clause      = []
    variables   = []
    current_clause = []

    for line in file:
        data = line.split()
        if len(data) == 0:
            continue
        if data[0] == 'c':
            continue
        if data[0] == 'p':
            tVariables  = int(data[2])
            tClauses    = int(data[3])
            continue
        if data[0] == '%':
            break
        if tVariables == -1 or tClauses == -1:
            print("Error, unexpected data")
            sys.exit(0)
        ##now data represents a clause
        for var_i in data:
            literal = int(var_i)
            if literal == 0:
                clause.append(current_clause)
                current_clause = []
                continue
            var = literal
            if var < 0:
                var = -var
            if var not in variables:
                variables.append(var)
            current_clause.append(literal)
    if tVariables != len(variables):
        print("Unexpected number of variables in the problem")
        print("Variables", tVariables, "len: ",len(variables))
        print(variables)
        sys.exit(0)
    if tClauses != len(clause):
        print("Unexpected number of clauses in the problem")
        sys.exit(0)
    file.close()

    return [variables, clause]


def random_initialization(variables):
    """
    Creates a random solution with 50% probability of each variable to be positive or negative
    :param variables: List of variables
    :return: A Random Initial list generated
    """
    rand_initial = []  # List to store literals
    for i in variables:  # Take each variable
        if random() <= 0.5:  # Have 50% probability of being positive or negative
            rand_initial.append(i)  # Positive if <= 0.5
        else:
            rand_initial.append(-i)  # Otherwise, Negative
    return rand_initial  # Return the Random Initial solution


def WalkSAT(sat_list, unsat_list, sol, tl, flip_iter_dic,c_iter):
    """
    Full WalkSAT + Tabu functionality is computed here.
    We Select a random clause, then check each variable from that to be in tabu or not,
    if not then we flip it & compute the negative gain & store in dictionary.
    Once done with all variables in that clause, we take variable with
    1. If negative_gain == 0, and flip it & return to update the main copy of the solution.
    2. Else, we compute random()<wp,
        i. If true, then take any variable from clause randomly which is not in tabu & flip it
            & return to update the main copy of the solution.
        ii. Else, take variable with minimum Negative Gain, and flip it & return to update the main copy of the solution
    :param sat_list: List of Sat Clauses
    :param unsat_list: List of Unsat Clauses
    :param sol: Current Main Solution
    :param tl: Length of tabu (Max no. of variable that can be stored)
    :param flip_iter_dic: Keeps the track of iterations where variables can be flipped next time
    :param c_iter: current iteration
    :return: True if Solution Found, ELse False & Updated version of sat_list, unsat_list, sol & tabu_dic
    """

    all_sat = sat_list + unsat_list  # Get all the clauses
    rand_unsat_clause = choice(unsat_list)  # Choose one clause at random from unsat clauses
    flipping = 0  # Flag to check if all variable of clause are tabu-ed,
                  # 0 == Yes, All tabu --> No, Flipping, vice-versa for 1
    b0 = 0  # Intialize b0, b1 with zeroes, used to calculated negative gain
    b1 = 0
    negative_gain_dic = {}  # Dictionary to store negative gain for each variable
    for var in rand_unsat_clause:  # Taking each var from chosen unsat clause
        # Check for give variable(key), what is the next iteration where it can flipped,
        # If its value is greater than current iteration, implies it is flipped with last tl moves,
        # hence can't be flipped. So, we move to next variable
        if flip_iter_dic[abs(var)] > c_iter:
            continue
        flipping = 1  # Turn the flag to one, because at least 1 variable have potential to be flipped
        for clause in sat_list:  # We take each clause from sat list
            if var in clause:  # check var from unsat_clause exist in this clausr or not
                b0 += 1  # increment b0 if exist
        # Make a copy of solution, we will flip var in this copy, we are using deepcopy() so that it doesn't make
        # changes to actual solution list. Deepcopy creates  new reference of same solution.
        sol_copy = deepcopy(sol)
        sol_copy[sol_copy.index(-var)] = var  # Flipping the variable in copied solution
        satisfied, unsat_list, _ = sat_sol(all_sat, sol_copy)  # Checking new solution in sat checker
        for clause in unsat_list:  # We take each clause from unsat list
            if var in clause:  # check var from unsat_clause exist in this clausr or not
                b1 += 1  # increment b1 if exist
        # appending the b0-b1--> Negative Gain, & Solution associated with var_flip
        negative_gain_dic[var] = (b0 - b1, sol_copy)

    if flipping == 1:  # Check flag, go ahead when at least 1 var have potential to be flipped
        neg_zero = [k for k, v in negative_gain_dic.items() if v[0] == 0]  # find all variables with neg gain == 0
        if len(neg_zero) != 0:  # If neg_zero list is not empty --> 1 or more var have neg_gain == 0
            var_flip = choice(neg_zero)  # Choose one var at random (breaking the ties)
        else:  # Neg_gain list is empty
            r = random()  # generate random between 0 & 1
            if r < wp:  # compare with wp
                # Choose any variable from unsat clause, which is not in tabu as var_flip
                var_flip = choice(list(negative_gain_dic.keys()))
            else:
                # Choose variable with minimum negative gain from unsat clause as var_flip
                min_neg_gain = min(negative_gain_dic.items(), key=operator.itemgetter(1))[1][0]
                # Check if there are multiple variable with minimum negative gain and choose one randomly
                var_flip = choice([k for k, v in negative_gain_dic.items() if v[0] == min_neg_gain])
        sol = negative_gain_dic[var_flip][1]  # Once we fix var_flip, find it's associated solution from neg_gain dictionary
        # update the next iteration where var_flip variable can be filpped next
        # this iteration will be tl iterations from current iteration. Hence current iter + tl
        flip_iter_dic[abs(var_flip)] = c_iter + tl
        # Check if solution exist or not for this solution
        satisfied, unsat_list, sat_list = sat_sol(all_sat, sol)

        if satisfied:  # If solution exist then return true, with other variables to be updated in main copy
            found = 1
            return [True, unsat_list, sat_list, sol, flip_iter_dic]
        # print("No Solution") # Else return False, with other variables to be updated in main copy
        return [False, unsat_list, sat_list, sol, flip_iter_dic]
    else: # As flipping flag == 0, implies no var from unsat clause can be flipped. Hence, No Solution found.
        return [False, unsat_list, sat_list, sol, flip_iter_dic]

# --------- CMD Input & Outer Variable initialization ---------
if len(sys.argv) < 7:
    print("Error - Incorrect input")
    print("Expecting python BasicTSP.py [instance] [#Executions] [#Restarts] [#Iterarions] [wp] [tl]")
    sys.exit(0)

variables, clauses = readFromFile(sys.argv[1])
executions = int(sys.argv[2])
restart = int(sys.argv[3])
iterations = int(sys.argv[4])
wp = float(sys.argv[5])
tl = int(sys.argv[6])

start_time = time.time()  # Time to check whole program execution

all_sol = []  # List to keep all valid solutions found
cpu_time_exec=[]  # List to store cpu time for RTD Plotting for each valid solution


# -----------LOOPS-----------
for full_exe in list(range(executions)):
    rand.seed(183770 + full_exe*1000)  # Random seed generation for each new execution
    start_process = time.time()  # Time to calculate the process time for each execution
    print("Executions -", full_exe)
    for i in list(range(restart)):  # no. of restarts
        rand_initial_sol = random_initialization(variables)  # Random initialization from variables
        satisfied, unsat_list, sat_list = sat_sol(clauses, rand_initial_sol)   # Checking random initial using sat_sol
        found = 0  # FLag to see if solution found or not
        sol = copy(rand_initial_sol)  # Make a copy of initial solution
        # Tabu Dic to store variables as keys and their next iteration where this variable can be flipped as value
        # Initializing all variable with 0, as any of them can be flipped
        tabu_dic = dict.fromkeys(sorted(variables), 0)
        for j in list(range(iterations)):
            # Check if solution exist in random initial, hence j == 0 (1st iteration)
            if len(unsat_list) == 0 and j == 0:
                found = 1  # If solution then change flag & break
                break
            #     Calling walkSat an updating unsat_list, sat_list, sol, tabu_dic with values returned by it
            chk, unsat_list, sat_list, sol, tabu_dic = WalkSAT(sat_list, unsat_list, sol, tl, tabu_dic, j)

            if chk:  # if chk == True, then solution found
                found = 1  # If solution then change flag & break
                break
        if found != 0:  # check solution found or not using found flag
            all_sol.append((full_exe, sorted(sol)))  # Append solution to list
            end_process = time.time()  # end time to check process timing
            cpu_time_exec.append((end_process - start_process))  # calculate time taken and append it with cpu timing
            break


# Printing the solutions
for i, each_sol in all_sol:
    print("Solution at Executions", i, ":", each_sol)

# Finding unique solutions
all_sol_dict = Counter(tuple(e[1]) for e in all_sol)
print("\nTotal Number of Unique solution:", len(all_sol_dict))
end_time = time.time()  # End time for full program execution
print("\nTime Taken For All Execution:", end_time - start_time, "secs\n")


# Sorting cpu execution time
print("CPU EXEC TIME EXEC WISE:\n")
cpu_time_exec = sorted(cpu_time_exec)
x = []  # For x-axis values
y = []  # For y-axis values
for i, tup in enumerate(cpu_time_exec):  # Enumerating & printing cputime(j) --> x vs j/execution --> y
    print(tup, (i+1)/executions)
    x.append(tup)
    y.append((i+1)/executions)

# Configuring the plot & printing it
plt.plot(x, y)
plt.title(sys.argv[1]+" WalkSAT"+"\nExec: "+sys.argv[2]+" | Restart: "+sys.argv[3]+" | Iteration: "+sys.argv[4]+" | wp: "+sys.argv[5]+" | tl: "+sys.argv[6])
plt.xlabel("Runtime/Execution (seconds)")
plt.ylabel("P(Solve)")
plt.grid(True)
plt.show()
