KELL_SIZE = 4
class BFMachine:
    def __init__(self):
        self.bootstrap()

    def bootstrap(self):
        self.tape = [0 for _ in range(13 * KELL_SIZE)]
        self.ptr = 0
        self.program_counter = 0
        self.output = []
        self.halted = False


    def do_left(self):
        assert (self.ptr > 0)
        self.ptr -= 1

    def do_right(self):
        self.ptr += 1

    def do_inc(self):
        self.tape[self.ptr] += 1

    def do_dec(self):
        assert(self.tape[self.ptr] > 0)
        self.tape[self.ptr] -= 1

    def do_out(self):
        self.output.append(self.tape[self.ptr])

    def do_in(self):
        pass

    def do_in_loop(self):
        def move_right():
            count = 1
            while count > 0:
                if self.program[self.program_counter] == '[':
                    count += 1
                elif self.program[self.program_counter] == ']':
                    count -= 1
                self.program_counter += 1
            assert (self.program[self.program_counter - 1] == ']')

        if self.tape[self.ptr] == 0:
            move_right()

    def do_out_loop(self):
        def move_left():
            count = 1
            while count > 0:
                if self.program[self.program_counter] == ']':
                    count += 1
                elif self.program[self.program_counter] == '[':
                    count -= 1
                self.program_counter -= 1
            assert (self.program[self.program_counter + 1] == '[')

        if self.tape[self.ptr] > 0:
            assert (self.program_counter >= 2)
            self.program_counter -= 2
            move_left()
            self.program_counter += 2

    def step(self):
        self.program_counter += 1
        {
            '<': self.do_left,
            '>': self.do_right,
            '+': self.do_inc,
            '-': self.do_dec,
            '.': self.do_out,
            ',': self.do_in,
            '[': self.do_in_loop,
            ']': self.do_out_loop
        }[self.program[self.program_counter - 1]]()

    def print_state(self):
        rest_of_program = self.program[self.program_counter:]
        if rest_of_program == '':
            rest_of_program = 'Empty Program'
        print self.program_counter, rest_of_program
        print 'Cell ', self.ptr, 'Kell ', self.ptr / KELL_SIZE
        i = 0
        s = ''
        while i < len(self.tape):
            s += '(' + ','.join(map(str, self.tape[i:i+KELL_SIZE])) + ') '
            i += KELL_SIZE
        print s
        print 'Halted' + str(self.output) if self.halted else 'Not halted ' + str(self.output)

    def run_code(self, program, fuel):
        self.halted = False
        self.program = program
        self.program_counter = 0

        for i in range(fuel):
            self.step()

            # Program halted
            if self.program_counter == len(self.program):
                self.halted = True
                return
        # Never halted but got out of fuel
        return

def firstDifferent(s):
    for i, c in enumerate(s):
        if c != s[0]:
            return i
    return len(s)

def closingBracket(rest):
    count = 1
    pc = 0
    while count > 0:
        if rest[pc] == '[':
            count += 1
        elif rest[pc] == ']':
            count -= 1
        pc += 1

    assert (rest[pc-1] == ']')
    return pc-1

def toCoq(bf_string):
    if len(bf_string) == 0:
        return 'bfn_end'
    split = firstDifferent(bf_string)
    c, rest = bf_string[0], bf_string[split:]
    if c == '[':
        closing = closingBracket(rest)
        body, end = rest[:closing], rest[closing+1:]
        return '(bfn_loop {} {})'.format(toCoq(body), toCoq(end))

    bfn_token = {
        '<': 'bfn_left',
        '>': 'bfn_right',
        '+': 'bfn_inc',
        '-': 'bfn_dec',
        '.': 'bfn_out',
        ',': 'bfn_in'
    }[c]
    return '({} {} {})'.format(bfn_token, split, toCoq(rest))
print toCoq('>>>[++<]>>-')


kl = KELL_SIZE * '<'
kr = KELL_SIZE * '>'

#set_zero = (KELL_SIZE - 3) * '>' + '+' + (KELL_SIZE - 2) * '<'
unmark = (KELL_SIZE - 2) * '>' + '+' + (KELL_SIZE - 2) * '<'
mark = (KELL_SIZE - 2) * '>' + '[-]' + (KELL_SIZE - 2) * '<'
next_marked = (KELL_SIZE - 2) * '>' + kr + '['+ kr + ']' + (KELL_SIZE - 2) * '<'
prev_marked = (KELL_SIZE - 2) * '>' + kl + '['+ kl + ']' + (KELL_SIZE - 2) * '<'
def write_scratch(n): return (KELL_SIZE - 1) * '>' + n * '+' + (KELL_SIZE - 1) * '<'

prev = kl + '[' + kl + ']'
next = kr + '[' + kr + ']'
zero_cell = '[-]'
scc_right = zero_cell + '>[-<+>]<'
scc_left = zero_cell + '<[->+<]>'
zero_kell = KELL_SIZE * (zero_cell + '>') + kl
empty_kell = zero_kell + (KELL_SIZE - 2) * '>' + '+' + (KELL_SIZE - 2) * '<'
#zero_item = zero_kell + kr + '[' + zero_kell + kr + ']'
empty_item = empty_kell + mark + kr + '[' + empty_kell + kr + ']' + prev_marked + unmark

def scc_right_n(n): return (n) * '>' + n * ('<' + scc_right)
shift_kell = KELL_SIZE * (scc_right_n(KELL_SIZE) + '>') + unmark + kl
sik = shift_kell + 2 * kr + '[' + kl + shift_kell + 2 * kr + ']' + kl + prev
shift_item = next + kl + '[' + sik + kl + ']' + sik
shift_scratch_left = kl + '[-' + kr + '+' + kl + ']' + kr
deref = (KELL_SIZE - 1) * '>' + '[' + kr + shift_scratch_left + '-]' + (KELL_SIZE - 1) * '<'



def push(n): return unmark + kr + unmark + '+>' + n * '+' + (KELL_SIZE - 1) * '>'
def delete(n):
    if n == 0:
        return prev + empty_item + mark
    return (n-1) * (prev + kr + mark + kl) + 2 * prev + shift_item + next + mark + next_marked + '[' + kl + shove_zero_gap + kr + unmark + next + mark + next_marked + ']' + prev_marked + stack_top


to_scratch = (KELL_SIZE - 1) * '>'
from_scratch = (KELL_SIZE - 1) * '<'
to_scratch_val = (KELL_SIZE - 2) * '>'
from_scratch_val = (KELL_SIZE - 2) * '<'

# assumes 'nonzero' and 'zero' will leave me in the same place; cleans up temps.
def if_else(nonzero, zero):
    return to_scratch + '[-]+' + kr + '[-]' + kl + from_scratch + '[' + nonzero + to_scratch + '-' + from_scratch + '[' + to_scratch + kr + '+' + kl + from_scratch + '-]]' + to_scratch + kr + '[' + from_scratch + kl + '+' + to_scratch + kr + '-]' + kl + '[' + from_scratch + zero + to_scratch + '-]'

# assumes 'nonzero'/'zero' will take me to a 0, and does not clean up any temps used.
# unpack can only work this way...
def garbage_if_else(nonzero, zero):
    return to_scratch + '[-]+' + kr + '[-]' + kl + from_scratch + '[' + nonzero + ']' + to_scratch + kr + '[' + from_scratch + kl + '+' + to_scratch + kr + '-]' + kl + '[' + from_scratch + zero + to_scratch + ']' + from_scratch

def if_else_val(nonzero, zero):
    return to_scratch_val + '[-]+' + kr + '[-]' + kl + from_scratch_val + '[' + nonzero + to_scratch_val + '-' + from_scratch_val + '[' + to_scratch_val + kr + '+' + kl + from_scratch_val + '-]]' + to_scratch_val + kr + '[' + from_scratch_val + kl + '+' + to_scratch_val + kr + '-]' + kl + '[' + from_scratch_val + zero + to_scratch_val + '-]'

def garbage_if_else_val(nonzero, zero):
    return to_scratch_val + '[-]+' + kr + '[-]' + kl + from_scratch_val + '[' + nonzero + ']' + to_scratch_val + kr + '[' + from_scratch_val + kl + '+' + to_scratch_val + kr + '-]' + kl + '[' + from_scratch_val + zero + to_scratch_val + ']' + from_scratch_val


# CODE FOR PACK/UNPACK + TESTS
unpack = prev + kr + '-' + garbage_if_else(kr + '[-' + kr + ']', '+' + next)

def pack(n):
    return prev * n + kr + ('+' + kr + '[+' + kr + ']') * n

stack_top = kr + '[[' + kr + ']' + kr + ']' + kl


shove_zero_gap = '<<[' + (KELL_SIZE-2) * '<' + shift_item + '<<]>>' + kl + shift_item
add_kell = '+>++>+>>'

to_scratch = (KELL_SIZE - 1) * '>'
from_scratch = (KELL_SIZE - 1) * '<'
def copy_to_scratch(offset):
    assert (offset < KELL_SIZE - 1)
    move = (KELL_SIZE - 1 - offset)
    return offset * '>' + '[-' + move * '>' + '+' + move * '<' + ']' + offset * '<'
def copy_cell(offset):
    prog = copy_to_scratch(offset)
    prog += to_scratch + '[-' + from_scratch + offset * '>' + '+' + offset * '<' + next_marked + offset * '>' + '+' + offset * '<' + prev_marked + to_scratch + ']' + from_scratch
    return prog

def get(n):
    prog = unmark + kr + mark + kl + (n+1) * prev + kr + mark
    prog += '[' + copy_cell(0) + copy_cell(1) + next_marked + unmark + prev_marked + unmark + kr + mark + ']'
    return prog + next_marked

# look at the value of the previous item. NOTE: this assumes that the last item
# is NOT a tuple; it gets the second element on the stack.
cond_get = prev + kr + '>' + garbage_if_else('<' + stack_top, '<' + stack_top + get(1))

bfm = BFMachine()
bfm.bootstrap()
# bfm.run_code(push(7) + push(3) + push(4) + push(0), 1500)
# bfm.print_state()

unpack_until_nat = kl + '-' + '[+' + kr + unpack + kl + '-]+' + kr

# main & [unpack until number left?] & prev > [ - garbage_if_else (/* non zero */ garbage_if_else (end) (< stack_top & delete 0 & f2 >)) (/* zero */ f1) ]

out = kl + '>.<' + kr
inc = kl + '>+<' + kr
dec = kl + '>-<' + kr
read = kl + '>,<' + kr

main = push(0) + push(0) + push(1) + push(0) + push(2) + out
# prog = unpack_until_nat + kl + '>[-' + garbage_if_else(garbage_if_else('', '<' + kr + delete(0) + out), '<' + kr + delete(0) + inc * 3 + out) + unpack_until_nat + kl + '>]'
prog_simpl = unpack_until_nat + kl + '>[-' + garbage_if_else_val('-' + garbage_if_else_val('-' + stack_top, '<' + kr + delete(0) + inc * 5 + out + delete(0) + stack_top), '<' + kr + delete(0) + inc * 3 + out + delete(0) + stack_top) + unpack_until_nat + kl + '>]'
# prog_very_simpl = unpack_until_nat + kl + '>'
# bfm.run_code(get(1), 1500)
# bfm.print_state()

bfm.run_code(main, 4000)
bfm.print_state()
bfm.run_code(prog_simpl, 5000)
bfm.print_state()
# bfm.run_code(unpack_until_nat + kl + '>', 200)
# bfm.print_state()
# bfm.run_code(unpack, 200)
# bfm.print_state()
# bfm.run_code(unpack, 200)
# bfm.print_state()
# bfm.run_code(unpack, 200)
# bfm.print_state()

# bfm.run_code(delete(3), 4500)
# bfm.print_state()
# bfm.run_code(cond_get, 4500)
# bfm.print_state()
