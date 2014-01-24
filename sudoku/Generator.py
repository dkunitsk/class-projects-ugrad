#Dmitriy Kunitskiy [SID# 26357420] & Valentin Yang [SID# 30062256]

import math
import random
import time
import copy
import sys
import argparse


class TimeOutException(Exception):
	def __init__(self, message):
		self.message = message

def parse_input_file(filename):
	f = open(filename, 'r')
	params = list(map(int, f.readline().strip('\n').split(' ')))

	if len(params)!=4 or params[0]!=params[1]*params[2] or params[3]>params[0]*params[0]:
		raise Exception
	next_line = f.readline()
	if not(next_line=='' or next_line=='\n'): 
		raise Exception
	f.close()

	global N, p, q, M
	N, p, q, M = params

def output_puzzle(filename, cells, domains, N, p, q):
	f = open(filename, 'w')
	output = ' '.join([str(N), str(p), str(q)]) + '\n'
	for i in range(N):
		row_i_cells = [cell for cell in cells[i*N : (i+1)*N]]
		output += ' '.join(''.join(domains[cell]) for cell in row_i_cells) + '\n'
	
	f.write(output)
	f.close()

def print_puzzle(cells, domains, N, p, q):
	"""This method uses code from P. Norvig's essay 'Solving Every Sudoku Puzzle.' 
	It was implemented for fun and is not part of the project requirements"""
	width = 1 + max(len(domains[cell]) for cell in cells)
	hor_line = '+'.join(['-'*(width*q)+'-']*(N//q))
	bar_cells = set(cell for cell in cells if (cell[1]+1)%q==0 and (cell[1]+1)//N!=1)
	for i in range(N):
		row_i_cells = [cell for cell in cells[i*N : (i+1)*N]]
		row_string = ' ' +' '.join(''.join(domains[cell]) + (' |' if cell in bar_cells else '') for cell in row_i_cells)
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
	token_list = [generate_token(i+1) for i in range(N)]
	cells = [(row,col) for row in [x for x in range(N)] for col in [y for y in range(N)]]
	cells_backup = copy.deepcopy(cells)

	row_peers = {cell : set(rv for rv in cells if rv[0]==cell[0]) - set([cell]) for cell in cells}
	col_peers = {cell : set(cv for cv in cells if cv[1]==cell[1]) - set([cell]) for cell in cells}
	blc_peers = {cell : set(bv for bv in cells if bv[0]>=(cell[0]//p)*p and bv[0]<((cell[0]//p)*p + p) and bv[1]>=(cell[1]//q)*q and bv[1]<((cell[1]//q)*q + q)) - set([cell]) for cell in cells}
	
	all_peers = {cell : col_peers[cell] | row_peers[cell] | blc_peers[cell] for cell in cells}

	return token_list, cells, cells_backup, all_peers

def search_for_puzzle_instance(*timeout_specified):
	token_list, cells, cells_backup, all_peers = environment_setup()

	domains = {cell : token_list[:] for cell in cells[:M]}	
	pruned_peer_dict = {cell : all_peers[cell].union([]) for cell in cells[:M]}

	puzzle_generated = False
	count = 0
	while not puzzle_generated:
		if timeout_specified:
			if time.time()-timeout_specified[1] >= timeout_specified[0]:
				raise TimeOutException('A timeout occurred')
		
		count += 1
		
		random.shuffle(cells)
		cells_M = cells[:M]

		domains = {cell : token_list[:] for cell in cells_M}	
		pruned_peer_dict = {cell : all_peers[cell].union([]) for cell in cells_M}
		"""
		To check for internal consistency at each assignment, we only need to 
		ensure that an assignment is consistent with previous assignments. 
		In this no-backtracking environment this allows us to eliminate 
		unassigned cells from each cell's set of peers. This is performed below.
		"""
		for i in range(M):
			pruned_peer_dict[cells_M[i]].intersection_update(cells_M[:i])

		for cell in cells_M:
			is_assigned = False
			while domains[cell]:
				value_to_try = random.choice(domains[cell])
				for peer in pruned_peer_dict[cell]:
					if value_to_try in domains[peer]:
						domains[cell].remove(value_to_try)
						break
				else:
					domains[cell] = [value_to_try]
					is_assigned = True
					break
			
			if not is_assigned:
				break
		else:
			puzzle_generated = True
	
	return domains, cells_backup


if __name__ == '__main__':
	################======== INPUT ARGUMENTS (start) ========################
	arg_parser = argparse.ArgumentParser(description='Generate a sudoku puzzle')
	arg_parser.add_argument('input_file', help='cd to the directory containing the input file and provide the filename; alternatively, provide the full filepath')
	arg_parser.add_argument('output_file', help='cd to the directory containing the output file and provide the filename; alternatively, provide the full filepath')
	arg_parser.add_argument('--timeout', '-t', help='optional timeout value (in seconds)', type=int)
	arg_parser.add_argument('--printsudoku', '-p', help='prints the generated puzzle instance to STDOUT', action='store_true')
	args = arg_parser.parse_args()
	input_filename = args.input_file
	output_filename = args.output_file
	timeout = args.timeout
	printsudoku = args.printsudoku
	################========  INPUT ARGUMENTS (end)  ========################
	t0 = time.time()

	if timeout:
		try:
			parse_input_file(input_filename)
			domains, cells_backup = search_for_puzzle_instance(timeout, t0)
		except TimeOutException:
			print('A timeout has occured because the puzzle took longer to generate than the (optional) specified maxiumum number of seconds')
			sys.exit()
		
	else:
		parse_input_file(input_filename)
		domains, cells_backup = search_for_puzzle_instance()

	complete_domains = {cell : domains[cell] if cell in domains else set(['0']) for cell in cells_backup}
	output_puzzle(output_filename, cells_backup, complete_domains, N, p, q)
	
	if printsudoku:
		print_puzzle(cells_backup, complete_domains, N, p, q)

	

