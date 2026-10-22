#define _GNU_SOURCE
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <libgen.h>
#include <limits.h>

int main(int argc, char *argv[]) {
    char exe_path[PATH_MAX];
    ssize_t len = readlink("/proc/self/exe", exe_path, sizeof(exe_path) - 1);
    if (len == -1) {
        perror("readlink /proc/self/exe");
        return 1;
    }
    exe_path[len] = '\0';

    char *dir = dirname(exe_path);
    char script_path[PATH_MAX];
    snprintf(script_path, sizeof(script_path), "%s/../../src/julia/Incremental-NC-Coins.jl", dir);

    char resolved_script[PATH_MAX];
    if (realpath(script_path, resolved_script) != NULL) {
        strncpy(script_path, resolved_script, sizeof(script_path));
    }

    char **new_argv = malloc((argc + 2) * sizeof(char *));
    if (!new_argv) {
        perror("malloc");
        return 1;
    }

    new_argv[0] = "julia";
    new_argv[1] = script_path;
    for (int i = 1; i < argc; i++) {
        new_argv[i + 1] = argv[i];
    }
    new_argv[argc + 1] = NULL;

    execvp("julia", new_argv);
    perror("execvp julia");
    free(new_argv);
    return 1;
}
