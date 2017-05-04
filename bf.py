class BFMachine:
    def __init__(self):
        self.bootstrap()

    def bootstrap(self):
        self.tape = [0 for _ in range(30)]
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
        print self.ptr, self.tape
        print 'Halted' if self.halted else 'Not halted'

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


prev = '<<<[<<<]'
next = '>>>[>>>]'
zero_cell = '[-]'
scc_right = zero_cell + '>[-<+>]<'
scc_left = zero_cell + '<[->+<]>'
zero_kell = zero_cell + '>' + zero_cell + '>' + zero_cell + '<<'
copy_kell = zero_cell + '>' + zero_cell + '>' + scc_right + '[->+<<<+>>]>>>' + scc_left + '[-<+<<<+>>>>]<<<<<'

def scc_right_n(n): return (n-1) * '>' + n * (scc_right + '<') + '>'
shift_kell = 3 * (scc_right_n(3) + '>') + '<<<'
sik = shift_kell + '>>>>>>[<<<' + shift_kell + '>>>>>>]<<<' + prev
shift_item = next + '<<<[' + sik + '<<<]' + sik

def push(n): return '>>>+>' + n * '+' + '>>'
def delete(n): return (n + 1) * prev + n * (shift_item + next) # + zero_item

bfm = BFMachine()
bfm.bootstrap()
bfm.run_code(push(3) + push(4), 100)
bfm.print_state()
bfm.run_code(prev + shift_kell + '<<<' + shift_kell, 1500)
bfm.print_state()
