import operator
import sys
import time
import random as rand
from collections import Counter
from copy import deepcopy
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
        vars = {}
        for literal in data:
            literal = int(literal)
            var = literal
            if var < 0:
                vars[-var] = 0
            else:
                vars[var] = 1
        return vars

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


def RandomWalk(unsat_list):
    """
    We randomly select clause from unsat clauses
    We randomly select a var to be flipped from this unsat clause
    :param unsat_list: List of unsat clauses
    :return: variable to be flipped
    """
    rand_unsat_clause = choice(unsat_list)  # Unsat clause selection
    rand_var = choice(rand_unsat_clause)  # Variable selection from chosen unsat clause
    # returning negative of selected variable(flip) because, only flipped version of this variable is present.
    # We want the current version of variable to be part of solution list, hence, it will be flipped back to current version from GWSAT function
    # While generating solution list
    return -rand_var


def GSAT(all_sat, unsat_count, sol):
    """
    This function performs GSAt.
    Makes a deepcopy of solution, so that any changes made to this copy won't be reflected in main copy until done explicitly
    :param all_sat: All Clauses List
    :param unsat_count: No. of unsat clauses in main/original solution
    :param sol: Current main/original solution
    :return: variable to be flipped
    """
    # Making a deep copy of solution to make changes that doesn't reflected in main solution
    sol_deep_copy1 = deepcopy(sol)
    net_gain_dic = {}  # Dictionary to store net gain for each variable
    b0 = unsat_count  # #Unsat Clauses in main solution
    for var in sol_deep_copy1:  # Taking each variable from copy of main solution
        sol_copy = deepcopy(sol)  # Making copy gain, to flip variables
        # Flipping each variable, i.e replace variable at it's current loaction with negative of it's value
        sol_copy[sol_copy.index(var)] = -var
        satisfied, unsat_list, sat_list = sat_sol(all_sat, sol_copy)  # Checking the new solution in sat_sol
        b1 = len(unsat_list)  # Getting updated number of unsat clauses after flip
        net_gain_dic[var] = (b0 - b1)  # calculate & store the net gain(b0-b1), against that variable
    # Once done with calculating net gain for all var, find the one with max net gain
    var_max_value = max(net_gain_dic.items(), key=operator.itemgetter(1))[1]
    # Check if there are multiple variable with max net-gain and choose one randomly from them (breaking ties)
    var_max_net = choice([k for k, v in net_gain_dic.items() if v == var_max_value])
    # Return the var to be flipped
    return var_max_net

def GWSAT(restart, iterations, variables, clauses, wp):
    """
    This fuction is ure pure GWSAT, with restarts, iterations, wp calculation & random_initlization.
    :param restart: #Restarts given by user
    :param iterations: #iterations given by user
    :param variables: # List of variables involved in all clauses
    :param clauses: 2D List of all clauses
    :param wp: walk probability
    :return: Solution List if solution found else -1
    """

    for i in list(range(restart)):
        rand_initial_sol = random_initialization(variables)  # Random initialization from variables
        satisfied, unsat_list, sat_list = sat_sol(clauses, rand_initial_sol)  # Checking random initial using sat_sol
        found = 0  # FLag to see if solution found or not
        sol = deepcopy(rand_initial_sol)  # Make a copy of initial solution

        for j in list(range(iterations)):
            # Check if solution exist in random initial, hence j == 0 (1st iteration)
            if len(unsat_list) == 0 and j == 0:
                return sol
            # Decide to do Random Walk or GSAT based on wp
            if random() < wp:
                flip_var = RandomWalk(unsat_list)  # Get var to be flipped
            else:
                flip_var = GSAT(unsat_list + sat_list, len(unsat_list), sol)  # Get var to be flipped
            sol[sol.index(flip_var)] = -flip_var  # Flip the variable in main solution copy
            # Check in solution exist using sat_sol
            chk, unsat_list, sat_list = sat_sol(sat_list+unsat_list, sol)
            # If solution exist, return it
            if chk:
                found = 1
                return sol
    # If solution doesn't exist in any restart, then return -1
    if found != 1:
        return -1

# --------- CMD Input & Outer Variable initialization ---------
if len(sys.argv) < 6:
    print("Error - Incorrect input")
    print("Expecting python BasicTSP.py [instance] [#Executions] [#Restarts] [#Iterarions] [wp]")
    sys.exit(0)

variables, clauses = readFromFile(sys.argv[1])
executions = int(sys.argv[2])
restart = int(sys.argv[3])
iterations = int(sys.argv[4])
wp = float(sys.argv[5])

start_time = time.time()
cpu_time_exec = []
all_sol = []

# -----------LOOPS-----------

for full_exe in list(range(executions)):
    rand.seed(183770 + full_exe*1000) # Random seed generation for each new execution
    print("Executions -", full_exe)
    start_process = time.time()  # Time to calculate the process time for each execution
    sol, itr = GWSAT(restart, iterations, variables, clauses,wp)  # Calling GWSAT - Core functionality

    if sol != -1:  # if solution exist, do this
        all_sol.append((full_exe,sorted(sol)))  # Append solution to list
        end_process = time.time() # end time to check process timing
        cpu_time_exec.append((end_process - start_process)) # calculate time taken and append it with cpu timing

    print('CPU Time:', end_process - start_process , 'for', full_exe)

# Printing the solutions
for i, each_sol in all_sol:
    print("Solution at Executions", i, ":", each_sol)

# Finding unique solutions
all_sol_dict = Counter(tuple(e[1]) for e in all_sol)
print("\nTotal Number of Unique solution:", len(all_sol_dict))
end_time = time.time() # End time for full program execution
print("\nTime Taken For All Execution:", end_time - start_time, "secs\n")

# Sorting cpu execution time
print("CPU EXEC TIME EXEC WISE:\n")
cpu_time_exec = sorted(cpu_time_exec)
x = []  # For x-axis values
y = []  # For y-axis values

# Enumerating & printing cputime(j) --> x vs j/execution --> y
for i, tup in enumerate(cpu_time_exec):
    print(tup, (i+1)/executions)
    x.append(tup)
    y.append((i+1)/executions)

# Configuring the plot & printing it
plt.plot(x, y)
plt.title(sys.argv[1]+" GWSAT"+"\nExec: "+sys.argv[2]+" | Restart: "+sys.argv[3]+" | Iteration: "+sys.argv[4]+" | wp: "+sys.argv[5])
plt.xlabel("Runtime/Execution (seconds)")
plt.ylabel("P(Solve)")
plt.grid(True)
plt.show()
