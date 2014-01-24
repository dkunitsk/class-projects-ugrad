#Dmitriy Kunitskiy [SID# 26357420] & Valentin Yang [SID# 30062256]
"""
Note: The solution heuristic employed in this assignment was heavily influenced by the 
suggestions found in Peter Norvig's essay, "Solving Every Sudoku Puzzle" (cited below). 
This degree of utilization of his published work is explicitly permited in R. Lathrop's
project specs for this assignment, as it was used solely for the purpose of learning about
sudoku and sudoku algorithms. Absolutely no code was copied directly or indirectly
from this article or anywhere else - although, due to the fact that we are exploiting
a good number of the design patterns suggested in his essay, some vague similarities between 
our solution and his published code may be present. If any such similarities are found, they
are entirely coindicental and will prove to be trivial.

	Norvig, P. (2010, August 20). Solving every sudoku puzzle. 
		Retrieved from http://norvig.com/sudoku.html
"""

import math
import random
import time
import copy
import sys
import argparse


class TimeOutException(Exception):
	def __init__(self, value):
		self.value = value
	def __str__(self):
		return repr(self.value)

def parse_input_file(filename):
	f = open(filename)
	line_1 = list(map(int, f.readline().strip('\n').split(' ')))
	if len(line_1) != 3 or line_1[0] != line_1[1]*line_1[2]: 
		raise Exception
	global N, p, q
	N, p, q = line_1
	
	puzzle_array = []
	for i in range(line_1[0]):
		row = list(f.readline().strip('\n').split(' '))
		puzzle_array.append(row)

	f.close()
	return puzzle_array

def output_puzzle(filename, state, cells, domains, N, p, q):
	f = open(filename, 'w')
	if state=='solved':
		output = ' '.join([str(N), str(p), str(q)]) + '\n'
		for i in range(N):
			row_i_cells = [cell for cell in cells[i*N : (i+1)*N]]
			output += ' '.join(''.join(domains[cell]) for cell in row_i_cells) + '\n'
		f.write(output)
	elif state=='timeout':
		f.write('Timeout')
	else:
		f.write('None')
	f.close()

def print_puzzle(cells, domains, N, p, q):
	"""This method uses code from P. Norvig's essay 'Solving Every Sudoku Puzzle.' 
	It was implemented for fun and is not part of the project requirements"""
	cell_width = max(len(domains[cell]) for cell in cells)
	width = 1 + cell_width
	hor_line = '+'.join(['-'*(width*q)+'-']*(N//q))
	bar_cells = set(cell for cell in cells if (cell[1]+1)%q==0 and (cell[1]+1)//N!=1)
	for i in range(N):
		row_i_cells = [cell for cell in cells[i*N : (i+1)*N]]
		row_string = ' ' +' '.join(' '*((cell_width - len(domains[cell]))//2) + ''.join(domains[cell]) + ' '*((cell_width - len(domains[cell]))//2) + (' ' if (cell_width - len(domains[cell]))%2 != 0 else '') + (' |' if cell in bar_cells else '') for cell in row_i_cells)
		print(row_string)
		if (i+1)%p==0 and (i+1)//N!=1:
			print(hor_line)
	print()

def generate_token(n):
	odigits = '123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'
	#subtract off the number of tokens which have fewer odometer-digits than the token that represents input n 
	exp = 0
	temp = n - math.pow(35, exp+1)
	while temp > 0: 
		n = temp
		exp += 1
		temp -= math.pow(35, exp+1)

	#assemble the token
	token = ''
	while exp >= 0:
		index = 0
		temp2 = n - math.pow(35, exp)
		while temp2 > 0:
			n = temp2
			index += 1
			temp2 -= math.pow(35, exp)
		token = token + odigits[index]
		exp -= 1
	return token

def environment_setup():
	puzzle_array = parse_input_file(input_filename) 

	token_list = [generate_token(i+1) for i in range(N)]
	cells = [(row,col) for row in [x for x in range(N)] for col in [y for y in range(N)]]
	cells_backup = copy.deepcopy(cells)

	row_peers = {cell : set(rv for rv in cells if rv[0]==cell[0]) - set([cell]) for cell in cells}
	col_peers = {cell : set(cv for cv in cells if cv[1]==cell[1]) - set([cell]) for cell in cells}
	blc_peers = {cell : set(bv for bv in cells if bv[0]>=(cell[0]//p)*p and bv[0]<((cell[0]//p)*p + p) and bv[1]>=(cell[1]//q)*q and bv[1]<((cell[1]//q)*q + q)) - set([cell]) for cell in cells}
	all_peers = {cell : col_peers[cell] | row_peers[cell] | blc_peers[cell] for cell in cells}

	domains = {cell : token_list[:] for cell in cells}

	def determine_no_peers_per_cell(N, p, q):
		return 2*(N-1) + p*q - p - q + 1 

	#Assign input puzzle values by iterating through the rows and columns 
	#of the input puzzle (stored as list of lists)
	for r in range(N):
		for c in range(N):
			cell_value = puzzle_array[r][c]
			if cell_value != '0':
				if cell_value not in token_list:
					raise Exception
				domains[(r, c)] = [cell_value]

	return token_list, cells, cells_backup, domains, all_peers

def solve_FC(max_time, start_time):
	"""Here we perform a preprocessing Forward Check on the cells which have been 
	predetermined in the parsed puzzle instance"""
	predetermined_cells = [cell for cell in cells if len(domains[cell])==1]
	for cell in predetermined_cells: 
		for peer in peers[cell]:
			try:
				domains[peer].remove(domains[cell][0])
				if not domains[peer]:
					#Puzzle contains internal inconsistencies
					return False, 0
			except ValueError:
				continue
	
	"""With FC, we can check constraint satisfaction by looking only at unassigned cells
	and making sure no unassigned cell's domains goes to cardinality of zero. This allows
	us to eliminate assigned cells from a cell's peer group"""
	for i in range(len(cells)):
		cell = cells[i]
		peers[cell] = [peer for peer in peers[cell] if peer in cells[i:]]

	domains_backup = copy.deepcopy(domains)
	def BT(recursion_depth, no_var_assignments):
		co_var = 0
		if time.time()-start_time >= max_time:
			raise TimeOutException(no_var_assignments)
		if recursion_depth == N*N:
			return True, no_var_assignments
		cell = cells[recursion_depth]
		domains_backup[cell] = domains[cell][:]
		for v in domains_backup[cell]:
			domains[cell] = [v]
			affected_peers = []
			for peer in peers[cell]:
				if v in domains[peer]:
					affected_peers.append(peer)
					domains[peer].remove(v)
					if not domains[peer]:
						break
			else:
				co_var += 1
				w = BT(recursion_depth + 1, no_var_assignments)
				if w[0]:
					return True, w[1] + co_var
			domains[cell] = domains_backup[cell][:]
			for peer in affected_peers:
				domains[peer] += [v]		
		return False, no_var_assignments + co_var
	
	return BT(0, 0)

def solve_noFC(max_time, start_time):
	"""With pure BT (no FC), we can check constraint satisfaction of a candidate assignment by 
	looking only at cells which were previously assigned (either through BT or because they
	were predetermined by the puzzle instance). This allows us to remove unassigned cells
	with unpruned domainss from a cell's peer group """
	predetermined_cells = [cell for cell in cells if len(domains[cell])==1]
	for i in range(len(cells)):
		cell = cells[i]
		if cell in predetermined_cells:
			peers[cell] = []
		else:
			peers[cell] = list(peers[cell].intersection(predetermined_cells + cells[:i]))

	domains_backup = copy.deepcopy(domains)
	def BT(recursion_depth, no_var_assignments):
		co_var = 0
		if time.time()-start_time >= max_time:
			raise TimeOutException(no_var_assignments)
		if recursion_depth >= N*N:
			return True, no_var_assignments
		cell = cells[recursion_depth] 
		domains_backup[cell] = domains[cell][:]
		for v in domains_backup[cell]:
			domains[cell] = [v]
			for peer in peers[cell]:
				if domains[peer] == [v]:
					break
			else:
				co_var += 1
				w = BT(recursion_depth + 1, no_var_assignments)
				if w[0]:
					return True, w[1]+co_var
			domains[cell] = domains_backup[cell]
		return False, no_var_assignments+co_var
	
	return BT(0, 0)


if __name__ == '__main__':
	t0 = time.time()

	################======== INPUT ARGUMENTS (start) ========################
	arg_parser = argparse.ArgumentParser(description='Solve a sudoku puzzle instance. By default, only Backtracking Search (BT) is performed. Use the supplied flags to switch on other heuristics')
	arg_parser.add_argument('input_file', help='cd to the directory containing the input file and provide the filename; alternatively, provide the full filepath')
	arg_parser.add_argument('--forwardchecking', '-f', help='turns on Forward Checking (FC)', action='store_true', default=False)
	arg_parser.add_argument('--timeout', '-t', help='timeout value (in seconds)', type=int, default = 60)
	arg_parser.add_argument('--writesolution', '-w', help='cd to the directory containing the output file where you would like the statistics to be written and provide the filename; alternatively, provide the full filepath')
	arg_parser.add_argument('--printsudoku', '-p', help='print the solved puzzle instance to STDOUT', action='store_true')
	args = arg_parser.parse_args()

	input_filename = args.input_file
	FC = args.forwardchecking
	timeout = args.timeout
	writesolution = args.writesolution
	printsudoku = args.printsudoku
	################========  INPUT ARGUMENTS (end)  ========################
	
	token_list, cells, cells_backup, domains, peers = environment_setup()

	if FC:
		stats = ''
		try:
			was_solved, nva = solve_FC(timeout, t0)
			stats += 'Time: ' + str(round((time.time()-t0)*1000, 2)) + '\n' + 'Assignments: ' + str(nva) + '\n' + 'Solution: ' + ('Yes \n' if was_solved else 'No \n') + 'Timeout: No'
			if writesolution:
				state = 'solved' if was_solved else 'None'
				output_puzzle(writesolution, state, cells, domains, N, p, q)

		except TimeOutException as inst:
			stats += 'Time: ' + str(round(time.time()*1000, 2)) + '\n' + 'Assignments: ' + str(0) + '\n' + 'Solution: No' + '\n' + 'Timeout: Yes'
			if writesolution:
				state = 'timeout'
				output_puzzle(writesolution, state, cells, domains, N, p, q)

		print(stats)
		
		if printsudoku:
			print_puzzle(cells, domains, N, p, q)

	else:
		stats = ''
		try:
			was_solved, nva = solve_noFC(timeout, t0)
			stats += 'Time: ' + str(round((time.time()-t0)*1000, 2)) + '\n' + 'Assignments: ' + str(nva) + '\n' + 'Solution: ' + ('Yes \n' if was_solved else 'No \n') + 'Timeout: No'
			if writesolution:
				state = 'solved' if was_solved else 'None'
				output_puzzle(writesolution, state, cells, domains, N, p, q)	

		except TimeOutException as inst:
			stats += 'Time: ' + str(round(time.time()*1000, 2)) + '\n' + 'Assignments: ' + str(0) + '\n' + 'Solution: No' + '\n' + 'Timeout: Yes'
			if writesolution:
				state = 'timeout'
				output_puzzle(writesolution, state, cells, domains, N, p, q)

		print(stats)
		
		if printsudoku:
			print_puzzle(cells, domains, N, p, q)








