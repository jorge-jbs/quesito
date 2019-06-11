@.str = private unnamed_addr constant [4 x i8] c"%d\0A\00", align 1

declare i32 @printf(i8*, ...)

define external ccc [0 x i8] @printInt(i32 %d, [0 x i8]) {
  %msg = getelementptr inbounds [4 x i8], [4 x i8]* @.str, i32 0, i32 0
  call i32 (i8*, ...) @printf(i8* %msg, i32 %d)
  ret [0 x i8] %0
}
