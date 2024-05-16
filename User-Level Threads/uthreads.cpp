#include "uthreads.h"
#include <queue>
#include <vector>
#include <iostream>
#include <algorithm>
#include <signal.h>
#include <unistd.h>
#include <sys/time.h>
#include <setjmp.h>

#ifdef __x86_64__
/* code for 64 bit Intel arch */

typedef unsigned long address_t;
#define JB_SP 6
#define JB_PC 7

/* A translation is required when using an address of a variable.
   Use this as a black box in your code. */
address_t translate_address (address_t addr)
{
  address_t ret;
  asm volatile("xor    %%fs:0x30,%0\n"
               "rol    $0x11,%0\n"
      : "=g" (ret)
      : "0" (addr));
  return ret;
}

#else
/* code for 32 bit Intel arch */

typedef unsigned int address_t;
#define JB_SP 4
#define JB_PC 5


/* A translation is required when using an address of a variable.
   Use this as a black box in your code. */
address_t translate_address(address_t addr)
{
    address_t ret;
    asm volatile("xor    %%gs:0x18,%0\n"
                 "rol    $0x9,%0\n"
    : "=g" (ret)
    : "0" (addr));
    return ret;
}
#endif

/* Data structure's */
enum State {
    READY,
    RUNNING,
    BLOCK,
    TERMINATED,
    SLEEP
};

struct Thread {
    int tid;
    State state;
    char stack[STACK_SIZE];
    sigjmp_buf env;
    int quantum_count;
    int total_sleep_quantums;
};

/* Error messages */
#define SIGACTION_ERR "error: sigaction error"
#define VTIME_ERR "error: setittime error"
#define UTHREAD_INIT_QUANTUM_ERR "error: failed init uthread since given quantum's number is negative"
#define UTHREAD_SPAWN_ERR "error: failed to spawn new"
#define UTHREAD_TERMINATE_ERR "error: failed to terminate thread tid: "
#define UTHREAD_BLOCK_ERR "error: failed to block thread tid: "
#define AVAILABLE_UTHREAD_NOT_FOUND "error: not found available thread: "
#define UTHREAD_RESUME_ERR "error: failed to resume thread tid: "
#define UTHREAD_SLEEP_ERR "error: failed to get in sleep: "
#define GET_THREAD_QUANTUM_ERR "error: illegal tid or given tid thread is blocked: "

/* Return values */
#define FAILED -1
#define SUCCESS 0
#define JUMPED_FROM_LONG 1

/* consts */
#define MAIN_TID 0
#define TIMING_FORMAT 1000000
#define SAVING_CONTEXT 0
#define FINISH_SLEEPING 0

/* Program Data */
static std::vector<Thread *> ready_queue;      /* Vector of pointers for ready threads */
static std::vector<Thread *> sleeping_threads; /* Vector of sleeping threads */
static Thread threads[MAX_THREAD_NUM];                         /* Array of possible threads */
static Thread *current_thread;                                 /* Current running thread */
static int total_threads = 0;                                  /* Amount of opened thread */
static int total_quantums = 0;  /* The amount of quantum's our all threads did to this moment */

/* pre-defined masker */
static sigset_t masked_set;                                    /* signal to mask */
struct sigaction sa = {};
#define BLOCK_VTIME_SIG sigprocmask(SIG_BLOCK, &masked_set, NULL)
#define UNBLOCK_VTIME_SIG sigprocmask(SIG_UNBLOCK, &masked_set, NULL)

/**
 * Set up a new thread
 * @param thread
 * @param entry_point
 */
void setup_thread (Thread *thread, thread_entry_point entry_point)
{
  address_t sp = (address_t) (*thread).stack + STACK_SIZE - sizeof (address_t);
  address_t pc = (address_t) entry_point;
  sigsetjmp((*thread).env, 1);
  ((*thread).env->__jmpbuf)[JB_SP] = translate_address (sp);
  ((*thread).env->__jmpbuf)[JB_PC] = translate_address (pc);
  sigemptyset (&(*thread).env->__saved_mask);
}

/**
 * Private helper function to get the minimal thread id which is not taken
 * @return tid
 */
int minimal_free_tid ()
{
  for (int i = 1; i < MAX_THREAD_NUM; i++)
    {
      if (threads[i].state == State::TERMINATED)
        {
          return i;
        }
    }
  std::cerr << AVAILABLE_UTHREAD_NOT_FOUND << std::endl;
  return FAILED;
}

/**
 * Remove the given thread tid from the sleeping vector
 * @param tid
 */
void remove_thread_from_sleeping (int tid)
{
  auto it = std::find (sleeping_threads.begin (), sleeping_threads.end (), &threads[tid]);

  // If the element was found, remove it
  if (it != sleeping_threads.end ())
    {
      sleeping_threads.erase (it); // Remove the element
    }
}

/**
 * Remove the given thread tid from the ready queue
 * @param tid
 */
void remove_thread_from_ready_queue (int tid)
{
  auto it = std::find (ready_queue.begin (), ready_queue.end (), &threads[tid]);

  // If the element was found, remove it
  if (it != ready_queue.end ())
    {
      ready_queue.erase (it); // Remove the element
    }
}

/**
 * Takes care on sleeping threads as: we keep vector of sleeping
 * threads and iterate over all the vector. Each thread we update his total_sleep_quantoms
 * and if total_sleep_quantoms == 0 then we remove the thread from the sleeping thread vector.
 * If the thread state isn't BLOCK then we add the thread to end of ready_queue if blocked we do nothing.
 * Observe that if thread been blocked while sleeping so we change his state from SLEEP to BLOCK and
 * the thread is yet on the sleeping vector until his sleep's time end.
 */
void update_sleeping_threads ()
{
  BLOCK_VTIME_SIG;
  std::vector<Thread *> new_sleeping_threads;
  for (auto thread: sleeping_threads)
    {
      (*thread).total_sleep_quantums--;

      if ((*thread).total_sleep_quantums == FINISH_SLEEPING)
        {
          if ((*thread).state == SLEEP)
            {
              (*thread).state = State::READY;
              ready_queue.push_back (thread);
            }
        }
      else
        {
          new_sleeping_threads.push_back (thread);
        }
      sleeping_threads = new_sleeping_threads;
      UNBLOCK_VTIME_SIG;
    }
}

/**
 * This function will handle the threads switching - called every time by to take care
 * of the singal SIGVTALRM which arriving from timer we also set at uthread_init()
 * This function is private implementation function
 */
void scheduler (int)
{
  /* In Case we save's the current thread, so:
   * 1) Make set running thread to READY state and push to the back of ready_queue.
   * 2) Take the next in queue_ready and set his state to RUNNING
   * 3) Restore the current thread context using siglongjmp
   */
  if (sigsetjmp((*current_thread).env, 1) == SAVING_CONTEXT)
    {
      if ((*current_thread).state != State::TERMINATED)
        {
          (*current_thread).state = State::READY;
          ready_queue.push_back (current_thread);
        }
      current_thread = ready_queue.front ();
      (*current_thread).state = State::RUNNING;
      ready_queue.erase (ready_queue.begin ());
      siglongjmp ((*current_thread).env, JUMPED_FROM_LONG);
    }
  else // In Case we came back from siglongjmp
    {
      update_sleeping_threads ();
      (*current_thread).quantum_count++;
      total_quantums++;
      // Now we finish and we return to our current thread
    }
}

/** ######################################################################### **/
/** ################################## API ################################## **/
/** ######################################################################### **/

int uthread_init (int quantum_usecs)
{
  // Validate quantum_usecs
  if (quantum_usecs <= 0)
    {
      std::cerr << UTHREAD_INIT_QUANTUM_ERR << std::endl;
      return FAILED;
    }

  // Init threads tid's by order
  for (int i = 1; i < MAX_THREAD_NUM; i++)
    {
      threads[i].quantum_count = 0;
      threads[i].state = State::TERMINATED;
      threads[i].tid = i;
    }

  sa.sa_handler = &scheduler;
  if (sigaction (SIGVTALRM, &sa, nullptr) < 0)
    {
      std::cerr << SIGACTION_ERR << std::endl;
      return FAILED;
    }
  sigemptyset (&masked_set);
  sigaddset (&masked_set, SIGVTALRM);

  // Init timer for whole program run time
  struct itimerval timer;
  // Configure the timer to expire after quantum_usecs virtual sec
  timer.it_value.tv_sec = quantum_usecs / TIMING_FORMAT;  // seconds part
  timer.it_value.tv_usec = quantum_usecs % TIMING_FORMAT; // microseconds part

  // Configure the timer to repeat after quantum_usecs virtual sec
  timer.it_interval.tv_sec = quantum_usecs / TIMING_FORMAT;
  timer.it_interval.tv_usec = quantum_usecs % TIMING_FORMAT;

  if (setitimer (ITIMER_VIRTUAL, &timer, nullptr) < 0)
    {
      std::cerr << VTIME_ERR << std::endl;
      return FAILED;
    }

  /* Here we set up the main thread with tid 0
   * Set total_quantom to 1 (by ex instruction) and set total opened threads as 0
   */
  total_quantums++;
  total_threads = 0;
  threads[MAIN_TID].tid = MAIN_TID;
  threads[MAIN_TID].state = State::RUNNING;
  threads[MAIN_TID].quantum_count = 1;
  setup_thread (&threads[MAIN_TID], nullptr);
  current_thread = &threads[MAIN_TID];
  return SUCCESS;
}

int uthread_spawn (thread_entry_point entry_point)
{
  BLOCK_VTIME_SIG;

  // Validate correctness - i.e: total_threads not pass the limit and entry_point isn't nullptr
  if (MAX_THREAD_NUM <= total_threads + 1 || entry_point == nullptr)
    {
      std::cerr << UTHREAD_SPAWN_ERR << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  /* Init new thread by finding minimal new available tid.
   * Change status of new thread to READY and push new thread to end of ready_queue.
   * Update total_threads.
   */
  int free_minimal_tid = minimal_free_tid ();
  setup_thread (&threads[free_minimal_tid], entry_point);
  threads[free_minimal_tid].state = State::READY;
  ready_queue.push_back (&threads[free_minimal_tid]); // add new thread pointer to the end of ready queue
  total_threads++;
  UNBLOCK_VTIME_SIG;
  return free_minimal_tid;
}

int uthread_terminate (int tid)
{
  BLOCK_VTIME_SIG;

  // Validate the correctness of tid
  if (tid < 0 || MAX_THREAD_NUM <= tid || threads[tid].state == State::TERMINATED)
    {
      std::cerr << UTHREAD_TERMINATE_ERR << tid << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  // Case of terminate main thread, so we need to exit the whole program
  if (tid == MAIN_TID)
    {
      exit (SUCCESS);
    }

  threads[tid].state = State::TERMINATED;
  total_threads--;

  // Current thread is not the one to terminate
  if (tid != current_thread->tid)
    {
      // In case the thread is in READY state
      if (threads[tid].state == State::READY)
        {
          remove_thread_from_ready_queue (tid);
        }

      // In case the thread is SLEEP/BLOCKED state
      if (threads[tid].state == State::SLEEP || threads[tid].state == State::BLOCK)
        {
          remove_thread_from_sleeping (tid);
        }
//      threads[tid].state = State::TERMINATED; // Set mode of thread to TERMINATED
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }

  // Terminate the current running thread - after termination will run the next thread in queue hence won't return
  if (tid == current_thread->tid)
    {
      current_thread = ready_queue.front ();
      current_thread->state = State::RUNNING;
      ready_queue.erase (ready_queue.begin ());
      UNBLOCK_VTIME_SIG;
      siglongjmp ((*current_thread).env, JUMPED_FROM_LONG);
    }

  UNBLOCK_VTIME_SIG;
  return SUCCESS;
}

int uthread_block (int tid)
{
  BLOCK_VTIME_SIG;

  // Validate the correctness of tid - also main thread tid 0 can't be blocked
  if (tid < 0 || MAX_THREAD_NUM <= tid || threads[tid].state == State::TERMINATED || threads[tid].tid == MAIN_TID)
    {
      std::cerr << UTHREAD_BLOCK_ERR << tid << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  // Case given thread state is BLOCKED - do nothing and return SUCCESS
  // Case given thread state is SLEEP - set state to BLOCKED and return SUCCESS
  if (threads[tid].state == State::BLOCK || threads[tid].state == SLEEP)
    {
      threads[tid].state = State::BLOCK;
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }

  // Case given thread state is READY - remove thread from ready_queue and set his state to BLOCKED
  if (threads[tid].state == State::READY)
    {
      remove_thread_from_ready_queue (tid);
      threads[tid].state = State::BLOCK;
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }

  // Case the given thread is running
  if (threads[tid].state == State::RUNNING)
    {
      threads[tid].state = State::BLOCK;
      if (sigsetjmp(threads[tid].env, 1) == JUMPED_FROM_LONG)
        {
          update_sleeping_threads ();
          current_thread->quantum_count++;
          total_quantums++;
          UNBLOCK_VTIME_SIG;
          return SUCCESS;
        }
      current_thread = ready_queue.front ();
      current_thread->state = State::RUNNING;
      ready_queue.erase (ready_queue.begin ());
      UNBLOCK_VTIME_SIG;
      siglongjmp (current_thread->env, JUMPED_FROM_LONG);
    }

  UNBLOCK_VTIME_SIG;
  return SUCCESS;
}

int uthread_resume (int tid)
{
  BLOCK_VTIME_SIG;

  // Validate the given tid
  if (tid < 0 || MAX_THREAD_NUM <= tid || threads[tid].state == State::SLEEP || threads[tid].state == State::TERMINATED)
    {
      std::cerr << UTHREAD_RESUME_ERR << tid << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  // Case of given tid is not blocked - if sleep/running/ready then ignore
  if (threads[tid].state == State::RUNNING || threads[tid].state == State::READY)
    {
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }

  // If the element was found on sleep list then change his state to SLEEP
  auto it = std::find (sleeping_threads.begin (), sleeping_threads.end (), &threads[tid]);
  if (it != sleeping_threads.end ())
    {
      Thread *thread = *it;
      (*thread).state = State::SLEEP;
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }

  // In case the thread is just BLOCK. (Not SLEEP)
  threads[tid].state = State::READY;
  ready_queue.push_back (&threads[tid]);

  UNBLOCK_VTIME_SIG;
  return SUCCESS;
}

int uthread_sleep (int num_quantums)
{
  BLOCK_VTIME_SIG;

  // Validate correctness - Only RUNNING thread can call this function!
  if (num_quantums < 0 || (*current_thread).tid == MAIN_TID)
    {
      std::cerr << UTHREAD_SLEEP_ERR << (*current_thread).tid << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  // Save the current context of function and will return 0 hence won't get-in
  // But when come-back from scheduler will return 1 - since return from longset hence will return SUCCES
  current_thread->state = State::SLEEP;
  current_thread->total_sleep_quantums = num_quantums;
  sleeping_threads.push_back (current_thread);

  if (sigsetjmp(current_thread->env, 1) == JUMPED_FROM_LONG)
    {
      update_sleeping_threads ();
      current_thread->quantum_count++;
      total_quantums++;
      UNBLOCK_VTIME_SIG;
      return SUCCESS;
    }
  current_thread = ready_queue.front ();
  current_thread->state = State::RUNNING;
  ready_queue.erase (ready_queue.begin ());
  UNBLOCK_VTIME_SIG;
  siglongjmp (current_thread->env, JUMPED_FROM_LONG);
}

int uthread_get_tid ()
{
  return current_thread->tid;
}

int uthread_get_total_quantums ()
{
  return total_quantums;
}

int uthread_get_quantums (int tid)
{
  BLOCK_VTIME_SIG;

  if (tid < 0 || MAX_THREAD_NUM <= tid || threads[tid].state == State::TERMINATED)
    {
      std::cerr << GET_THREAD_QUANTUM_ERR << tid << std::endl;
      UNBLOCK_VTIME_SIG;
      return FAILED;
    }

  UNBLOCK_VTIME_SIG;
  return threads[tid].quantum_count;
}
