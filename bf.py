KELL_SIZE = 4
class BFMachine:
    def __init__(self):
        self.bootstrap()

    def bootstrap(self):
        self.tape = [0 for _ in range(10 * KELL_SIZE)]
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
        print 'Halted' + str(self.output) if self.halted else 'Not halted'

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

KELL_SIZE = 4
kl = KELL_SIZE * '<'
kr = KELL_SIZE * '>'

next_nonzero = (KELL_SIZE - 2) * '>'
def write_scratch(n): return (KELL_SIZE - 1) * '>' + n * '+' + (KELL_SIZE - 1) * '<'

prev = kl + '[' + kl + ']'
next = kr + '[' + kr + ']'
zero_cell = '[-]'
scc_right = zero_cell + '>[-<+>]<'
scc_left = zero_cell + '<[->+<]>'
zero_kell = KELL_SIZE * (zero_cell + '>') + '<<+' + (KELL_SIZE - 2) * '<'
copy_kell = zero_cell + '>' + zero_cell + '>' + scc_right + '[->+<<<+>>]>>>' + scc_left + '[-<+<<<+>>>>]<<<<<'
zero_item = zero_kell + kr + '[' + zero_kell + kr + ']'

def scc_right_n(n): return (n) * '>' + n * ('<' + scc_right)
shift_kell = KELL_SIZE * (scc_right_n(KELL_SIZE) + '>') + kl
sik = shift_kell + 2 * kr + '[' + kl + shift_kell + 2 * kr + ']' + kl + '+' + prev
cik = copy_kell + 2 * kr + '[' + kl + copy_kell + 2 * kr + ']' + kl + copy_kell + prev
shift_item = next + kl + '[' + sik + kl + ']' + sik
shift_scratch_left = kl + '[-' + kr + '+' + kl + ']' + kr
deref = (KELL_SIZE - 1) * '>' + '[' + kr + shift_scratch_left + '-]' + (KELL_SIZE - 1) * '<'


def push(n): return kr + '+>' + n * '+' + (KELL_SIZE - 1) * '>'
def delete(n): return (n + 1) * prev + n * (shift_item + next) + zero_item

# assumes 'nonzero' and 'zero' will leave me in the same place; cleans up temps.
def if_else(nonzero, zero):
    return '>>[-]+>>>[-]<<<<<' + '[' + nonzero + '>>-<<[>>>>>+<<<<<-]]' + '>>>>>[<<<<<+>>>>>-]<<<[<<' + zero + '>>-]'

# assumes 'nonzero'/'zero' will take me to a 0, and does not clean up any temps used.
# unpack can only work this way...
def garbage_if_else(nonzero, zero):
    return '>>[-]+>>>[-]<<<<<' + '[' + nonzero + ']' + '>>>>>[<<<<<+>>>>>-]<<<[<<' + zero + '>>]<<'


# CODE FOR PACK/UNPACK + TESTS
unpack = prev + '>>>-' + garbage_if_else('>>>[->>>]', '+' + next)

def pack(n):
    return prev * n + '>>>' + ('+>>>[+>>>]') * n
stack_top = kr + '[[' + kr + ']' + kr + ']' + kl

bfm = BFMachine()
bfm.bootstrap()
bfm.run_code(push(3) + push(4) + push(5), 100)
bfm.run_code(3 * prev, 1500)
bfm.run_code(write_scratch(5), 1500)
bfm.print_state()
bfm.run_code(deref, 1500)
bfm.print_state()
