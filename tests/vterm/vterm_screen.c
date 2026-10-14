// SPDX-FileCopyrightText: Copyright (C) 2026 David Stainton
// SPDX-License-Identifier: AGPL-3.0-only

// What libvterm makes of bytes, for Tessera's differential test.
//
//   vterm_screen screen COLS ROWS   reads output from stdin and prints the screen, a row a line,
//                                   each cell's characters, the right half of a wide character
//                                   left out; then "#title " and the title, if one was set.
//   vterm_screen widths             reads characters, one a line, and prints the cells libvterm
//                                   gives each, a number a line.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <vterm.h>

static char title[4096];
static size_t title_len;
static int title_set;

static int settermprop(VTermProp prop, VTermValue *val, void *user) {
  (void)user;
  if (prop == VTERM_PROP_TITLE) {
    if (val->string.initial) title_len = 0;
    size_t n = val->string.len;
    if (title_len + n > sizeof title - 1) n = sizeof title - 1 - title_len;
    memcpy(title + title_len, val->string.str, n);
    title_len += n;
    title[title_len] = 0;
    title_set = 1;
  }
  return 1;
}

static void put_utf8(uint32_t c) {
  char b[4];
  int n;
  if (c < 0x80) { b[0] = c; n = 1; }
  else if (c < 0x800) { b[0] = 0xC0 | c >> 6; b[1] = 0x80 | (c & 0x3F); n = 2; }
  else if (c < 0x10000) { b[0] = 0xE0 | c >> 12; b[1] = 0x80 | (c >> 6 & 0x3F); b[2] = 0x80 | (c & 0x3F); n = 3; }
  else { b[0] = 0xF0 | c >> 18; b[1] = 0x80 | (c >> 12 & 0x3F); b[2] = 0x80 | (c >> 6 & 0x3F); b[3] = 0x80 | (c & 0x3F); n = 4; }
  fwrite(b, 1, n, stdout);
}

static char *read_all(size_t *len) {
  size_t cap = 1 << 16, n = 0;
  char *buf = malloc(cap);
  size_t r;
  while ((r = fread(buf + n, 1, cap - n, stdin)) > 0) {
    n += r;
    if (n == cap) buf = realloc(buf, cap *= 2);
  }
  *len = n;
  return buf;
}

static VTerm *open_vterm(int rows, int cols, VTermScreen **screen) {
  VTerm *vt = vterm_new(rows, cols);
  vterm_set_utf8(vt, 1);
  *screen = vterm_obtain_screen(vt);
  vterm_screen_reset(*screen, 1);
  return vt;
}

static int screen_mode(int cols, int rows) {
  VTermScreen *screen;
  VTerm *vt = open_vterm(rows, cols, &screen);
  static VTermScreenCallbacks cb = {.settermprop = settermprop};
  vterm_screen_set_callbacks(screen, &cb, NULL);
  size_t len;
  char *buf = read_all(&len);
  vterm_input_write(vt, buf, len);
  for (int row = 0; row < rows; row++) {
    for (int col = 0; col < cols;) {
      VTermScreenCell cell;
      vterm_screen_get_cell(screen, (VTermPos){.row = row, .col = col}, &cell);
      if (cell.chars[0] == 0) putchar(' ');
      for (int i = 0; i < VTERM_MAX_CHARS_PER_CELL && cell.chars[i]; i++) put_utf8(cell.chars[i]);
      col += cell.width > 0 ? cell.width : 1;
    }
    putchar('\n');
  }
  if (title_set) printf("#title %s\n", title);
  vterm_free(vt);
  return 0;
}

static int widths_mode(void) {
  VTermScreen *screen;
  VTerm *vt = open_vterm(1, 8, &screen);
  char line[64];
  while (fgets(line, sizeof line, stdin)) {
    size_t n = strcspn(line, "\n");
    vterm_input_write(vt, "\x1b[H\x1b[2J", 7);
    vterm_input_write(vt, line, n);
    VTermScreenCell cell;
    vterm_screen_get_cell(screen, (VTermPos){.row = 0, .col = 0}, &cell);
    printf("%d\n", cell.chars[0] ? cell.width : 0);
  }
  vterm_free(vt);
  return 0;
}

int main(int argc, char **argv) {
  if (argc == 4 && strcmp(argv[1], "screen") == 0) return screen_mode(atoi(argv[2]), atoi(argv[3]));
  if (argc == 2 && strcmp(argv[1], "widths") == 0) return widths_mode();
  fprintf(stderr, "usage: %s screen COLS ROWS | widths\n", argv[0]);
  return 2;
}
