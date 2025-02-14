# Dynamic memory allocator

This is a dynamic memory allocator.

- Free block organization: segregated ordered free lists, each is an explicit free list without footers.
- Placement policy: first fit in ordered lists, equivalent to best fit.
- Coalecsing policy: immediate coalecsing.

Check `mm.c` for more details.