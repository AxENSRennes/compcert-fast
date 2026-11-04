/* Measurement harness. Distributed under the repository's INRIA license.
   The same clang-built harness is linked to each compiler's benchmark object.
   QoS is advisory: macOS provides no supported exclusive P-core affinity. */
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/qos.h>

extern int benchmark_main(int argc, char **argv);

int main(int argc, char **argv)
{
    struct timespec begin, end;
    int qos_error = pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
    if (qos_error) {
        fprintf(stderr, "QoS request failed: %d\n", qos_error);
        return 125;
    }
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &begin)) return 125;
    int result = benchmark_main(argc, argv);
    /* Include output flushing, exclude process creation and dynamic loading. */
    if (fflush(stdout)) return 125;
    if (clock_gettime(CLOCK_MONOTONIC_RAW, &end)) return 125;
    double seconds = (double)(end.tv_sec - begin.tv_sec)
                   + (double)(end.tv_nsec - begin.tv_nsec) * 1e-9;
    fprintf(stderr, "COMPCERT_FAST_TIME %.9f\n", seconds);
    return result;
}
