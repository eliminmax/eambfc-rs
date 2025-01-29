A brainfuck program that prints a utf8 zombie emoji using a technique that
requires wrapping and gets corrupted if overflow affects adjacent cells

set cells 1 through 4 to 0xf0
++++++++++++++++[->->->->-<<<<]
set cell 0 to 81 for use in the next step
>>>>>+++++++++[-<<<<<+++++++++>>>>>]<<<<<
set cells 2 through 4 to 0x9f by subtracting 81
[>>->->-<<<<-]
set cell 3 to 0xa7 by adding 8
>>>++++++++
go back to the null byte at the start
[<]
print all non-null bytes in a row
>[.>]
