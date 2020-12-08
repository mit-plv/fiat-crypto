/* Note: These constants must match the values put in the record compiler.MemoryLayout,
   and they must satisfy compiler.MemoryLayoutOk. */

stack_size    = 1M;
heap_size     = 1M;
code_start    = 0x10000000;
heap_start    = 0x20000000;
stack_pastend = 0x40000000;

stack_start = stack_pastend - stack_size;

SECTIONS
{
  . = code_start;
  /* objdump puts the binary produced by the compiler into a data section */
  .text : { *(.data) }

  . = heap_start;
  .heap (NOLOAD): {
    . = . + heap_size;
  }

  . = stack_start;
  .stack (NOLOAD): {
    . = . + stack_size;
  }
}
