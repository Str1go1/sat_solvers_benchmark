import tkinter as tk
from tkinter import ttk
import random
import time
import tracemalloc
import copy
import sys
import threading
sys.setrecursionlimit(2000)

#solvcers
#1 resolution solver
def resolution_solver(clauses):
    processed_clauses = []
    for c in clauses:
        clause_set = set(c)
        if any(-l in clause_set for l in clause_set):
            continue  # Skip tautologies
        processed_clauses.append(clause_set)

    clauses = processed_clauses
    if set() in clauses:
        return False
    if not clauses:
        return True

    known_clauses = set(frozenset(c) for c in clauses)
    new_pairs = True

    while new_pairs:
        new_pairs = False
        new_resolvents = set()

        clause_list = list(known_clauses)
        for i in range(len(clause_list)):
            for j in range(i + 1, len(clause_list)):
                Ci, Cj = clause_list[i], clause_list[j]
                for l in Ci:
                    if -l in Cj:
                        resolvent = (Ci | Cj) - {l, -l}
                        if any(-lit in resolvent for lit in resolvent):
                            continue
                        if not resolvent:
                            return False
                        resolvent_frozen = frozenset(resolvent)
                        if resolvent_frozen not in known_clauses:
                            new_resolvents.add(resolvent_frozen)

        if new_resolvents:
            known_clauses.update(new_resolvents)
            new_pairs = True

    return True

#2 dp alogorithm
def unit_propagate(clauses):
    assignment = {}
    changed = True
    while changed:
        changed = False
        clauses = [c for c in clauses if not any(-lit in c for lit in c)]
        if not clauses:
            return clauses, assignment
        
        for c in clauses:
            if len(c) == 0:
                return None
            if len(c) == 1:
                unit = next(iter(c))
                assignment[abs(unit)] = (unit > 0)
                new_clauses = []
                for d in clauses:
                    if unit in d:
                        continue
                    if -unit in d:
                        d = d.copy()
                        d.remove(-unit)
                    new_clauses.append(d)
                clauses = new_clauses
                changed = True
                break
    return clauses, assignment

def pure_literal_assign(clauses):
    assignment = {}
    all_literals = {lit for c in clauses for lit in c}
    for lit in list(all_literals):
        if -lit not in all_literals:
            assignment[abs(lit)] = (lit > 0)
            clauses = [c for c in clauses if lit not in c]
            all_literals = {lit for c in clauses for lit in c}
    return clauses, assignment

def dp_solver(clauses):
    def preprocess(clauses):
        processed = []
        for c in clauses:
            s = set(c)
            if not any(-l in s for l in s):
                processed.append(s)
        return processed

    clauses = preprocess(clauses)

    if not clauses:
        return True

    result = unit_propagate(clauses)
    if result is None:
        return False
    clauses, _ = result

    clauses, _ = pure_literal_assign(clauses)
    if not clauses:
        return True

    all_literals = {lit for c in clauses for lit in c}
    pivots = {abs(l) for l in all_literals if -l in all_literals}
    if not pivots:
        return all(len(c) > 0 for c in clauses)

    pivot = next(iter(pivots))

    pos_clauses = [c for c in clauses if pivot in c]
    neg_clauses = [c for c in clauses if -pivot in c]
    other_clauses = [c for c in clauses if pivot not in c and -pivot not in c]

    new_clauses = []
    for c in pos_clauses:
        for d in neg_clauses:
            resolvent = (c | d) - {pivot, -pivot}
            if any(-lit in resolvent for lit in resolvent):
                continue 
            if len(resolvent) == 0:
                return False
            new_clauses.append(resolvent)
        # Avoid clause duplication
    all_clauses = {frozenset(c) for c in other_clauses}
    for nc in new_clauses:
        frozen = frozenset(nc)
        if frozen not in all_clauses:
            all_clauses.add(frozen)

    return dp_solver([set(c) for c in all_clauses])


#dpll algorithm
def dpll(clauses, assignment=None):
    if assignment is None:
        assignment = {}
    processed_clauses = []
    for c in clauses:
        clause_set = set(c)
        is_tautology = False
        for l in list(clause_set):
            if -l in clause_set:
                is_tautology = True
                break
        if not is_tautology:
            processed_clauses.append(clause_set)
    
    clauses = processed_clauses
    if not clauses:
        return True
    
    changed = True
    while changed:
        changed = False
        for c in clauses:
            if len(c) == 0:
                return False
            if len(c) == 1:
                unit = next(iter(c))
                assignment[abs(unit)] = (unit > 0)
                new_clauses = []
                for d in clauses:
                    if unit in d:
                        continue
                    if -unit in d:
                        d = d.copy()
                        d.remove(-unit)
                    new_clauses.append(d)
                clauses = new_clauses
                changed = True
                break
    clauses = [c for c in clauses if not any(-lit in c for lit in c)]
    if not clauses:
        return True
    
    all_literals = {lit for c in clauses for lit in c}
    for lit in list(all_literals):
        if -lit not in all_literals:
            assignment[abs(lit)] = (lit > 0)
            clauses = [c for c in clauses if lit not in c]
            all_literals = {lit for c in clauses for lit in c}
    if not clauses:
        return True
    first_clause = clauses[0]
    lit = next(iter(first_clause))
    new_clauses = [c.copy() for c in clauses] + [{lit}]
    if dpll(new_clauses, assignment.copy()):
        return True
    new_clauses = [c.copy() for c in clauses] + [{-lit}]
    return dpll(new_clauses, assignment.copy())
#random 3-SAT
def generate_random_3sat(n_vars, n_clauses, seed=None):
    if seed is not None:
        random.seed(seed)
    cnf = []
    for _ in range(n_clauses):
        clause = set()
        while len(clause) < 3:
            lit = random.randint(1, n_vars)
            lit *= random.choice([-1, 1])
            clause.add(lit)
        cnf.append(list(clause))
    return cnf
def format_clause(clause):
    def lit_str(l):
        return f"x{abs(l)}" if l > 0 else f"¬x{abs(l)}"
    return "(" + " ∨".join(lit_str(lit) for lit in clause) + ")"

def format_cnf(cnf):
    return "∧".join(format_clause(clause) for clause in cnf)
#benchmarking
def benchmark_algorithms_threaded():
    global benchmark_running
    benchmark_running = True
    
    def safe_insert(text):
        if benchmark_running:
            output_box.after(0, output_box.insert, tk.END, text)

    #output_box.after(0, output_box.delete, 1.0, tk.END)
    sizes = [4,6,8,10,12,14,16,18,20]
    algorithms = {
        "Resolution": resolution_solver,
        "DP": dp_solver,
        "DPLL": dpll
    }
    for n in sizes:
        if not benchmark_running:
            break
            
        m = 4 * n
        cnf = generate_random_3sat(n, m, seed=n)
        formatted_cnf = format_cnf(cnf)
        safe_insert(f"\nCNF with {n} vars, {m} clauses\n")
        safe_insert(f"{formatted_cnf}\n")
        safe_insert("\n")
        for name, solver in algorithms.items():
            if not benchmark_running:
                break
            if name == "Resolution" and n > 8:
                safe_insert(f"{name:10} | Skipped (n > 8)\n")
                continue
                
            tracemalloc_started = False
            try:
                tracemalloc.start()
                tracemalloc_started = True
                start_time = time.perf_counter()
                result = solver(copy.deepcopy(cnf))
                end_time = time.perf_counter()
                _, peak = tracemalloc.get_traced_memory()
                elapsed = end_time - start_time
                mem_usage = peak / (1024 * 1024)
            except RecursionError:
                result = "RecursionError"
                elapsed = 0
                mem_usage = 0
            except Exception as e:
                result = f"Error: {type(e).__name__}"
                elapsed = 0
                mem_usage = 0
            finally:
                if tracemalloc_started:
                    tracemalloc.stop()

            safe_insert(
                f"{name:10} | Time: {elapsed:.4f} s | Memory: {mem_usage:.2f} MB | Result: {result}\n"
            )
        safe_insert("-" * 70 + "\n")
    
    benchmark_running = False
    run_button.configure(text="Run Benchmarks")
    cancel_button.configure(state="disabled")

def run_benchmark_thread():
    global benchmark_running
    if benchmark_running:
        return
        
    benchmark_running = True
    run_button.configure(text="Running...")
    cancel_button.configure(state="normal")
    threading.Thread(target=benchmark_algorithms_threaded).start()
    
def cancel_benchmark():
    global benchmark_running
    benchmark_running = False
    output_box.insert(tk.END, "\n[Benchmark cancelled by user]\n")
    run_button.configure(text="Run Benchmarks")
    cancel_button.configure(state="disabled")

#tkinter gui
root = tk.Tk()
root.title("SAT Solver Benchmark GUI")
benchmark_running = False
frame = ttk.Frame(root, padding=10)
frame.grid(row=0, column=0)

run_button = ttk.Button(frame, text="Run Benchmarks", command=run_benchmark_thread)
run_button.grid(row=0, column=0, pady=10, padx=5)

cancel_button = ttk.Button(frame, text="Cancel", command=cancel_benchmark, state="disabled")
cancel_button.grid(row=0, column=1, pady=10, padx=5)

output_box = tk.Text(root, height=30, width=100)
output_box.grid(row=1, column=0, padx=10, pady=10)

if __name__ == "__main__":
    root.mainloop()