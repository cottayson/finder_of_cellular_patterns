// к работе:
// [x] добавить комбинированные решения
// [x] добавить методы реального времени (при редактировании прямо тут же применять комбинированные решения)
// [+] добавить ручное редактирование stowage
// [+] убрать процедуру копирования copy3dArray, применив указатель sip(быстрый поиск в глубину) 
//     [+] запоминаем все действия в подзадаче, и откатываем их назад при возвращении к исходной задаче
// [ ] undo history + отход назад если противоречие
// [ ] избавиться от границ и попытаться от прочих догм
// [ ] обобщить до произвольного графа
// [?] добавить алгоритм решающий булевы и рекурсивные формулы например понятие суммы
//     [+] добавить понятие суммы
//     [ ] добавить булевы формулы
//     [ ] добавить рекурсивные формулы 
// [ ] максимально плотное объединение(union) недезинтегрированных решений (т.е. все остальные кроме дубликатов)
// (позволяет убрать симметричные решения, чтобы в множестве решений не было дубликатов и union был более информативным для человека)
// решение: unionA отображается в минимальный unionB, состоящий из решений не приводимых друг к другу симметриями, которые переводят в себя unionA
// изучить монотонные фунции и найти остальные миры кроме линейных
// изучить построение электронных схем
// обдумать модель "игру" социального взаимодействия нейронов
let logic = [];
let globalUnionArray = []
let stowage = [];
let defaultStowage = []
let errors = [];
let solves = [];

let BG_COLOR =     [125, 125, 125] // [100, 100, 100]
let GRID_COLOR =   [ 60,  60,  60] // [0, 0, 0]
let POINTS_COLOR = [255,   0, 255]
let ZERO_COLOR =   [  0,   0,   0] // [255, 255, 255]
let ONE_COLOR =    [225, 225,   0] // [0, 125, 125]
let ERROR_COLOR =  [255,   0,   0]
let TEXT_COLOR =   [  0,   0,   0] // [0, 0, 0]
let STABLE_COLOR = [  0, 255,   0] // [0, 0, 0]

let logicSize = {w: 12, h: 12, z: 2};
let rectSize = 30;
let offset = {x: 50, y: 10};
offset.dy = (logicSize.h + 1) * rectSize;
let textOffset = {x: 10, y: 21};
// counts {
let n = 0, maxPreSolveIterations = 0, 
  maxSetOfChangesLength = 0, 
  solutionsCount = 0;
// counts }
let listOfSymbols = [' ', 'o', '*', 'E']
let lengthOfLogicSet = 2;
let defaultPavement = 0; // lengthOfLogicSet <=> *
let maxPrint = 5000
let randomFilter = 0.01
let maxStowage = 0
let maxBranches = 150000
let debugStep = 50000
let preSolveEnable = true
let errorUpgrade = true

let unionAutoEnable = false
let autoPlace = false
let functionalSymmetryEnable = false
let zeroBorders = true
let zLoopBack = true

function put(i, j) {
  for(let kk = 0; kk < logicSize.z; kk++) {
    if(stowage.length >= maxStowage + defaultStowage.length)
      return
    else
      putToStowage(i, j, kk)
  }
}

function makeDiagonalStowage() {
  let wh = logicSize.w + logicSize.h
  for(let i = 0; i < wh; i++) {
    for(let j = 0; j <= i; j++) {
      let x = i - j
      let y = j
      if(x < logicSize.w && y < logicSize.h) {
        put(x, y)
      }
    }
  }
}

function makeLinearStowage() {
  for(let i = 0; i < logicSize.w; i++) {
    for(let j = 0; j < logicSize.h; j++) {
      for(let k = 0; k < logicSize.z; k++) {
        if(stowage.length >= maxStowage) {
          break
        } else {
          putToStowage(i, j, k)
        }
      }
    }
  }
}

const tests = {
  sumTest: {
    enabled: false,
    target: 0,
    dt: 0,
  },
  kernelSumTest: {
    enabled: false,
    target: 1,
    dt: Infinity,
  },
  stableTest: {
    enabled: true,
    listOfPoints: [],
  },
  callbackList: [sumTestCallback, kernelTestCallback, stableTestCallback],
}

tests.stableTest.listOfPoints.add = function(x, y) {
  if(x === undefined || y === undefined) throw "input must be two arguments (x, y)"
  let list = tests.stableTest.listOfPoints
  
  for(let i = list.length - 1; i >= 0; i--) {
    if(list[i].x === x && list[i].y === y) {
      list.splice(i, 1)
      return false
    }
  }
  // otherwise
  list.push({x, y})
  return true
}

tests.stableTest.listOfPoints.remove = function(x, y) {
  if(x === undefined || y === undefined) throw "input must be two arguments (x, y)"
  let list = tests.stableTest.listOfPoints
  for(let i = list.length - 1; i >= 0; i--) {
    if(list[i].x === x && list[i].y === y) {
      list.splice(i, 1)
    }
  }
  return tests.stableTest.listOfPoints
}

tests.stableTest.listOfPoints.clear = function() {
  let list = tests.stableTest.listOfPoints
  list.splice(0, list.length)
  return tests.stableTest.listOfPoints
}

function stableTestCallback(arr) {
  // use .bind to reduce args length to one when test launched
  // or make global testOptions object
  const testOptions = tests.stableTest
  //-------------------------------------------------------------------------------------
  if(testOptions.enabled === false) {
    return true
  }
  
  if(logicSize.z < 2) {
    // throw "logicSize.z < 2 => stableTest should not be used"
    return true
  }
  //-------------------------------------------------------------------------------------
  let listOfPoints = testOptions.listOfPoints
  for(let i = 0; i < listOfPoints.length; i++) {
    let point = listOfPoints[i]
    let firstCell = arr[point.x][point.y][0]
    if(firstCell === 2) {
      continue
    }
    // firstCell < 2
    for(let k = 1; k < logicSize.z; k++) {
      let otherCell = arr[point.x][point.y][k]
      if(otherCell === 2) {
        continue
      }
      // otherCell < 2 AND firstCell < 2
      if(otherCell !== firstCell) {
        // not stable column of cells
        return false
      }
    }
  }
  return true
}

function kernelTestCallback(arr) {
  const testOptions = tests.kernelSumTest
  //-------------------------------------------------------------------------------------
  if(testOptions.enabled === false) {
    return true
  }
  
  if(logicSize.z < 2) {
    // throw "logicSize.z < 2 => kernelTest should not be used"
    return true
  }
  const targetsum = {min: testOptions.target, max: testOptions.target + testOptions.dt}
  //-------------------------------------------------------------------------------------

  let total = {min: 0, max: 0}
  for(let j = 0; j < logicSize.h; j++) {
    for(let i = 0; i < logicSize.w; i++) {
      let firstCell = arr[i][j][0]
      let secondCell = arr[i][j][1]
      if(firstCell === 2 || secondCell === 2) {
        total.max += 1
      } else if(firstCell !== secondCell) {
        total.min += 1
        total.max += 1
      }
    }
  }
  
  // [targetsum.min targetsum.max] < [total.min total.max]
  // [total.min total.max] < [targetsum.min targetsum.max]
  
  if( total.min > targetsum.max || total.max < targetsum.min ) {
    return false
  }
  return true
}

function sumTestCallback(arr) {
  const testOptions = tests.sumTest
  //-------------------------------------------------------------------------------------
  if(testOptions.enabled === false) {
    return true
  }
  const targetsum = {min: testOptions.target, max: testOptions.target + testOptions.dt}
  //-------------------------------------------------------------------------------------
  let total = {min: 0, max: 0}
  for(let j = 0; j < logicSize.h; j++) {
    for(let i = 0; i < logicSize.w; i++) {
      for(let k = 0; k < logicSize.z; k++) {
        let cell = arr[i][j][k]
        if(cell === 2) {
          total.max += 1
        } else {
          total.min += cell
          total.max += cell
        }
      }
    }
  }
  if(!(total.min <= targetsum.max && total.max >= targetsum.min)) {
    return false
  }
  return true
}

function globalSolve() {
  // initialize union array with empty sets "E"
  globalUnionArray = init3DArray(logicSize.w, logicSize.h, logicSize.z, 3)
  let arr = copy3dArray(logic);
  stowage = []
  for(let u = 0; u < defaultStowage.length; u++) {
    let point = defaultStowage[u]
    stowage.push({
      i: point[0],
      j: point[1],
      k: point[2],
    })
  }
  makeDiagonalStowage()
  // global variables
  solves = []
  n = 0; maxPreSolveIterations = 0;
  maxSetOfChangesLength = 0;
  solutionsCount = 0
  // global variables
  console.log("solutions: ")
  let sip = 0, changedPos = null
  console.time('solve time')
  solve(arr, sip, changedPos)
  console.timeEnd('solve time')
  const foundedAllSolutions = n < maxBranches
  if(unionAutoEnable) {
    applyUnion()
  } else {
    console.log('union: ')
    print3dSolve(globalUnionArray /*union(solves)*/)
  }
  // no recursion
  if(foundedAllSolutions)
    console.log("all " + solutionsCount /*solves.length*/ + " solutions found.");
  else
    console.log("solutions = " + solutionsCount /*solves.length*/);
  console.log("branches = " + n);
  if(preSolveEnable) {
    console.log("maxPreSolveIterations = " + maxPreSolveIterations);
    console.log("maxSetOfChangesLength = " + maxSetOfChangesLength);
  }
}

//**********************************************************************************
function unionTo(solution, unionArray) {
  for(let i = 0; i < logicSize.w; i++)
    for(let j = 0; j < logicSize.h; j++)
      for(let k = 0; k < logicSize.z; k++) {
        let cell = solution[i][j][k]
        let unionCell = unionArray[i][j][k]
        unionArray[i][j][k] = logicUnion(unionCell, cell)
      }
}

function applyUnion() {
  const foundedAllSolutions = n < maxBranches
  // print3dSolve(unionArray)
  if(solutionsCount > 0 && foundedAllSolutions) {
    logic = copy3dArray(globalUnionArray)
    return true
  }
  return false
}

function union(solutions) {
  let unionArray = init3DArray(logicSize.w, logicSize.h, logicSize.z, 3);
  for(let index = 0; index < solutions.length; index++) {
    let solution = solutions[index]
    for(let i = 0; i < logicSize.w; i++)
      for(let j = 0; j < logicSize.h; j++)
        for(let k = 0; k < logicSize.z; k++) {
          let cell = solution[i][j][k]
          let unionCell = unionArray[i][j][k]
          unionArray[i][j][k] = logicUnion(unionCell, cell)
        }
  }
  return unionArray
}

function setZeroBorders() {
  for(let k = 0; k < logicSize.z; k++) {
    for(let i = 0; i < logicSize.w; i++) {
      logic[i][0][k] = 0;
      logic[i][logicSize.h - 1][k] = 0;
    }

    for(let i = 0; i < logicSize.h; i++) {
      logic[0][i][k] = 0;
      logic[logicSize.w - 1][i][k] = 0;
    }
  }
}

function changeLogicSizeBy(dw, dh, dz, _zeroBorders = false) {
  resizeLogicTo(logicSize.w + dw, logicSize.h + dh, logicSize.z + dz, _zeroBorders)
}

function resizeLogicTo(w, h, z, _zeroBorders = false) {
  let minSize = { 
    w: Math.min(logicSize.w, w), 
    h: Math.min(logicSize.h, h),
    z: Math.min(logicSize.z, z),
  }
  let temp = copy3dArray(logic)
  logicSize = {w, h, z}
  initialization(_zeroBorders)
  // fill current logic array with values
  for(let i = 0; i < minSize.w; i++)
    for(let j = 0; j < minSize.h; j++)
      for(let k = 0; k < minSize.z; k++)
        logic[i][j][k] = temp[i][j][k]
      
  draw() // what if call draw() 1000000 times? you can replace it by setting draw flag (needRedrawInThisTick) and add draw function in timer
}

function initialization(_zeroBorders = false) {
  offset.dy = (logicSize.h + 1) * rectSize
  let size = {
    w: (logicSize.w+1) * rectSize + offset.x - 10, 
    h: logicSize.z    * offset.dy + offset.y - 10
  }
  resizeCanvas(size.w, size.h)
  logic = init3DArray(logicSize.w, logicSize.h, logicSize.z, 2);
  if(_zeroBorders) {
    setZeroBorders()
  }
  draw()
}

function setup() {
  createCanvas(0, 0)
  offset.x = windowWidth / 2 + 200
  noLoop();
  textFont("consolas", 20);
  initialization(zeroBorders)
  
  // logic[1][1][0] = 0; logic[2][1][0] = 0; logic[3][1][0] = 0; logic[4][1][0] = 0; logic[5][1][0] = 0;
  // logic[1][2][0] = 0; logic[2][2][0] = 0; logic[3][2][0] = 0; logic[4][2][0] = 0; logic[5][2][0] = 0;
  // logic[1][3][0] = 0; logic[2][3][0] = 1; logic[3][3][0] = 1; logic[4][3][0] = 1; logic[5][3][0] = 0;
  // logic[1][4][0] = 0; logic[2][4][0] = 0; logic[3][4][0] = 0; logic[4][4][0] = 0; logic[5][4][0] = 0;
  // logic[1][5][0] = 0; logic[2][5][0] = 0; logic[3][5][0] = 0; logic[4][5][0] = 0; logic[5][5][0] = 0;
}

function functionalSymmetry(i, j, k) {
  //return {i: logicSize.w - i - 1, j: j};
  let di = 2, dj = 2;
  if(i < di || i >= logicSize.w - di || j < dj || j >= logicSize.h - dj)
    return {i: i, j: j, k: (k + 1) % 2};
  return {i: i, j: j, k: k};
}

let shiftPressed = false
let controlPressed = false
function keyReleased() {
  if(keyCode == SHIFT) {
    shiftPressed = false
  }
  if(keyCode == CONTROL) {
    controlPressed = false
  }
}

function keyPressed() {
  if(keyCode == SHIFT) {
    shiftPressed = true
  }
  if(keyCode == CONTROL) {
    controlPressed = true
  }
  if(keyCode == 85) { // u
    if(applyUnion()) {
      console.log('union applied')
    } else {
      console.log('not all solutions found or solutionsCount = 0')
    }
  }
  if(keyCode == 187) { // "="
    if(autoPlace) {
      autoPlace = false;
      console.log("autoPlace -disabled.");
    } else {
      autoPlace = true;
      console.log("autoPlace +enabled.");
    }
  }
  if(keyCode == ENTER) {
    let detect = detectErrors(logic);
    if(!detect) {
      console.clear();
      globalSolve();
    } else {
      console.log("detectErrors = ", detect);
    }
  }
  //********************************************************************************
  draw();
}

function mousePressed() {
  let i = floor((mouseX - offset.x) / rectSize);
  let j = floor((mouseY - offset.y) / rectSize) % (logicSize.h + 1);
  let k = floor((mouseY - offset.y) / offset.dy);
  if(i >= 0 && i < logicSize.w && j >= 0 && j < logicSize.h && k >= 0 && k < logicSize.z) {
    if(shiftPressed) {
      if(mouseButton == LEFT) {
        if(addToStowage(defaultStowage, [i, j, k])) {
          console.log('added point to defaultStowage',[i, j, k])
        } else {
          console.log('removed point from defaultStowage',[i, j, k])
        }
      } else if(mouseButton == RIGHT) {
        defaultStowage = []
        console.log('defaultStowage cleared')
      }
    } else if(controlPressed) {
      if(mouseButton == LEFT) {
        if( tests.stableTest.listOfPoints.add(i, j) ) {
          console.log('added point to StableTest', [i, j])
        } else {
          console.log('removed point from StableTest', [i, j])
        }
      } else if(mouseButton == RIGHT) {
        tests.stableTest.listOfPoints.clear()
        console.log('StableTest list cleared')
      }
    } else {
      let value;
      if(mouseButton == LEFT) {
        if(logic[i][j][k] != 1) value = 1; else value = 2;
      } else 
      if(mouseButton == RIGHT) {
        if(logic[i][j][k] != 0) value = 0; else value = 2;
      }
      if(mouseButton != CENTER) {
        if(autoPlace) {
          for(let z = 0; z < logicSize.z; z++)
            logic[i][j][z] = value;
        } else {
          logic[i][j][k] = value;
        }
      }
    }
  }
  if(shiftPressed == false) {
    let detect = detectErrors(logic);
    if(detect) {
      console.clear();
    }
    console.log("detectErrors = ", detect);
  }
  //********************************************************************************
  draw();
}

function addToStowage(stow, point) {
  for(let i = 0; i < stow.length; i++) {
    let pointInStow = stow[i]
    let equal = true
    for(let j = 0; j < 3; j++) {
      equal = equal && (pointInStow[j] === point[j])
    }
    if(equal == true) { // если такая уже есть
      stow.splice(i, 1) // удаляем
      return false // скажем что удалили
    }
  }
  stow.push(point) // добавляем точку
  return true
}

function putToStowage(i, j, k) {
  if(logic[i][j][k] < 2)
    return false;
  stowage.push({i, j, k});
  return true;
}
 // исправлено
function draw() {
  background(BG_COLOR)
  stroke(GRID_COLOR)
  drawBackground(offset.x, offset.y, offset.dy, logic)
  for(let z = 0; z < logicSize.z; z++) {
    drawGrid(offset.x, offset.y + offset.dy * z, logicSize.w, logicSize.h, rectSize)
  }
  drawText(offset.x + textOffset.x, offset.y + textOffset.y, logic)
  for(let i = 0; i < defaultStowage.length; i++) {
    let point = defaultStowage[i]
    drawPoint(point[0], point[1], point[2], POINTS_COLOR)
  }
  for(let i = 0; i < tests.stableTest.listOfPoints.length; i++) {
    let point = tests.stableTest.listOfPoints[i]
    for(let z = 0; z < logicSize.z; z++) {
      drawPoint(point.x, point.y, z, STABLE_COLOR, 'S')
    }
  }
}

function drawPoint(x, y, z, color, character) {
  if(character === undefined) {
    noFill()
    strokeWeight(3)
    stroke(color)
    rect(
      offset.x + rectSize * x, 
      offset.y + rectSize * y + offset.dy * z,
      rectSize, rectSize
    )
    strokeWeight(1)
  } else {
    noStroke()
    fill(color)
    text(
      character,
      textOffset.x + offset.x + rectSize * x,
      textOffset.y + offset.y + rectSize * (y+0.0) + offset.dy * z
    )
  }
}
//**********************************************************************************
 // исправлено
function preSolveError(arr, setOfChanges) {
let changes = false;
// let mainError = isError(arr, changedPos);
// if(mainError) {
  // return 1;
// }
//changedPos = {i: -1, j: -1}; // changedPos is empty => absolutely no Errors in all cells
  // это не пригодится
for(let i = 0; i < logicSize.w; i++)
  for(let j = 0; j < logicSize.h; j++)
    for(let k = 0; k < logicSize.z; k++) {
      let cell = arr[i][j][k]
      if(cell == 2) {
        arr[i][j][k] = 0
        changedPos = {i, j, k}
        let zeroErr = isError(arr, changedPos);
        arr[i][j][k] = 1
        let oneErr = isError(arr, changedPos)
        if(!zeroErr && !oneErr) {
          // 0 0 => x = ?
          // массив не меняется
          arr[i][j][k] = 2;
        } else {
          // запоминаем изменение массива
          setOfChanges.push(changedPos)
          if(zeroErr && oneErr) { // 1 1 => x = []
            return 1; // error
          } else
          if(zeroErr) { // 1 0 => x = 1
            arr[i][j][k] = 1;
            changes = true;
          } else
          if(oneErr) { // 0 1 => x = 0
            arr[i][j][k] = 0;
            changes = true;
          }
        }
      }
    }
if(changes) {
  return 2; // no error but some changes detected
  } else {
  return 0; // no changes no error
  }
}
 // работает
function isError(arr, changedPos) {
  // launch test callbacks
  for(let i = 0; i < tests.callbackList.length; i++) {
    let testCallback = tests.callbackList[i]
    if(testCallback(arr) == false) {
      return true
    }
  }

  if(changedPos != null) {
    let x = changedPos.i;
    let y = changedPos.j;
    let z = changedPos.k;
    for(let i = x - 1; i <= x + 1; i++)
      for(let j = y - 1; j <= y + 1; j++)
        for(let k = z - 1; k <= z + 1; k++) { // действительно ли это так или можно это упростить
          let actualK
          if(zLoopBack) {
            actualK = (k + logicSize.z) % logicSize.z
          } else {
            actualK = k
            if(k === 0) continue
          }
          
          if( notInRange(i, j, actualK, logicSize.w, logicSize.h, logicSize.z) )
            continue;
          if(valueError(arr, i, j, actualK))
            return true;
        }
    return false;
  }
  let startK = zLoopBack ? 0 : 1
  for(let i = 0; i < logicSize.w; i++)
    for(let j = 0; j < logicSize.h; j++)
      for(let k = startK; k < logicSize.z; k++)
        if(valueError(arr, i, j, k))
          return true;
  return false;
}
// работает
function valueError(arr, i, j, k, detect) {
  let cell = arr[i][j][k];
  if(cell == 2) return false;
  // cell != 2
  if(functionalSymmetryEnable) {
    let fSym = functionalSymmetry(i, j, k);
    let symCell = arr[fSym.i][fSym.j][fSym.k];
    if(symCell != 2) { // if cell != 2 and symCell != 2
      if(symCell != cell) {
        if(detect != undefined) {
          errors.push({i, j, k});
        }
        return true;
      }
    }
  }
  if(errorInCell(arr, i, j, k)) {
    if(detect != undefined) {
      console.log("error at ", i, j, k);
      errors.push({i, j, k});
    }
    return true;
  }
  return false;
}
 // исправлено
function isRandomFiltering() {
  if(randomFilter < 1) {
    return Math.random() < randomFilter
  } else {
    return true
  }
}

function solve(arr, sip, changedPos, setOfChanges = []) {
  if(n >= maxBranches) {
    return;
  }
  n++;
  if(n % debugStep == 0) {
  console.log(`{${n}}`)
  }
  if(setOfChanges.length > 0) {
    throw new Error('такого не бывает')
  }
  if(errorUpgrade == false) {
    changedPos = null;
  }
  // detect errors for cut one branch
  if( isError(arr, changedPos) ) {
    return;
  }
  if(preSolveEnable) {
    // для того чтобы обратить все изменения в presolve
    // их все нужно запомнить
    let iterations = 1;
    // копия ссылки, массив не копируется
    let temp = arr
    // let temp = copy3dArray(arr)
    // some manipulations for presolve
    let pre = preSolveError(temp, setOfChanges)
    while(pre == 2) { // some changes detected
      pre = preSolveError(temp, setOfChanges)
      iterations++
    }
    if(iterations > maxPreSolveIterations) {
      maxPreSolveIterations = iterations
    }
    if(setOfChanges.length > maxSetOfChangesLength) {
      maxSetOfChangesLength = setOfChanges.length
    }
    
    if(pre == 1) { // error detected
      return;
    }
    // in this line pre always equal zero
  }
  // some stuff
  if(sip >= stowage.length) {
    // add successful branch to solves
    // solves.push( copy3dArray(arr) ) // THIS CODE LINE TAKES UP A LOT OF MEMORY
    unionTo(arr, globalUnionArray)
    solutionsCount++
    
    if(solutionsCount <= maxPrint && isRandomFiltering()) {
      print3dSolve(arr, solutionsCount)
    }
    return;
  }
  let stow = stowage[sip];
  let si = stow.i, sj = stow.j, sk = stow.k;
  sip++;
  let cell = arr[si][sj][sk];
  while (cell < 2 && sip < stowage.length) { // if cell is constant
    stow = stowage[sip];
    si = stow.i; sj = stow.j; sk = stow.k;
    sip++;
    cell = arr[si][sj][sk];
    //console.log("CONSTANT USING", "sip = " + sip);
  }
  let previousValue = cell // не всегда = 2
  // recursive call solve()
  // if(previousValue != 2) {
    // console.log('previousValue != 2: stow', stow)
  // }
  for(let value = 0; value < 2; value++) {
    let pos = {i: si, j: sj, k: sk};
    arr[si][sj][sk] = value
    // выделяем массив для изменений на уровне ниже
    let levelDownSetOfChanges = []
    solve(arr, sip, pos, levelDownSetOfChanges)
    for(let i = 0; i < levelDownSetOfChanges.length; i++) {
      let curPos = levelDownSetOfChanges[i]
      arr[curPos.i][curPos.j][curPos.k] = 2
      // console.log('curPos: ', curPos)
    }
    arr[si][sj][sk] = previousValue
  }
  
  // for(let value = 0; value < 2; value++) {
    // let pos = {i: si, j: sj, k: sk};
    // let temp = copy3dArray(arr);
    // temp[si][sj][sk] = value;
    // solve(temp, sip, pos);
  // }
  return;
}
 // исправлено
function printSolve(arr, n) {
  let str = "";
  if(n != undefined)
    str += n + ")\n";
  for(let i = 0; i < logicSize.h; i++) {
    for(let j = 0; j < logicSize.w; j++) {
      str += getSymbol(arr[j][i]) + " ";
    }
    str += "\n";
  }
  console.log(str);
}

function print3dSolve(arr, n) {
  let str = "";
  if(n != undefined)
    str += n + ")\n";
  for(let k = 0; k < logicSize.z; k++) {
    str += " *** t = " + (k+1) + " *** \n";
    for(let i = 0; i < logicSize.h; i++) {
      for(let j = 0; j < logicSize.w; j++) {
        str += getSymbol(arr[j][i][k]) + " ";
      }
      str += "\n";
    }
  }
  console.log(str);
}
 // осталось исправить
function loadToArray(arr, load, offsetX, offsetY) {
  for(let i = 0; i < load.length; i++)
    for(let j = 0; j < load[0].length; j++) {
      let i_ = j + offsetX, j_ = i + offsetY;
      if(i_ < 0 || i_ >= logicSize.w || j_ < 0 || j_ >= logicSize.h)
        continue;
      arr[i_][j_] = load[i][j];
    }
}
// исправлено
function notInRange(i, j, k, w, h, z) {
  return (i < 0 || i >= w || j < 0 || j >= h || k < 0 || k >= z);
}
// исправлено
function getCell(arr, i, j, k, w, h, z) {
  if(notInRange(i, j, k, w, h, z))
    return defaultPavement;
  return arr[i][j][k];
}
// наверное исправлено
// cell = 0 => sum != 3
function errorInCell(arr, x, y, z) {
  let minSum = 0, maxSum = 0;
  // потом нужно исправить эту строку
  let mainCell = arr[x][y][z];
  let k = (z - 1 + logicSize.z) % logicSize.z; // предполагая положительный обход вдось оси z
  let prevCell = arr[x][y][k];
  if(mainCell == 2)
    return false;
     
  // TEST STUFF
  if(zLoopBack === false) {
    if(z === 0) {
      throw `z === ${z} AND zLoopBack === false`
    }
  }

  for(let i = x - 1; i <= x + 1; i++)
    for(let j = y - 1; j <= y + 1; j++) {
      if(i == x && j == y) continue;
      let cell = getCell(arr, i, j, k, logicSize.w, logicSize.h, logicSize.z);
      if(cell == 2) {
        maxSum++;
      } else {
        maxSum += cell;
        minSum += cell;
      }
    }
  
  if(prevCell == 2) {
    if(mainCell == 0)
      if(minSum == 3 && maxSum == 3) // sum = 3
        return true;
    if(mainCell == 1)
      if(minSum > 3 || maxSum < 2) // sum not in {2, 3}
        return true;
  }
  
  if(mainCell == 0) {
    if(prevCell == 0)
      if(minSum == 3 && maxSum == 3) // sum = 3
        return true;
    if(prevCell == 1)
      if(minSum >= 2 && maxSum <= 3) // сумма должна быть только либо 2 либо 3
        return true;
    /* возможны три варианта:
    1. только 2 
    2. только 3
    3. внутри отрезка [2, 3]
    */
  }
  if(mainCell == 1) {
    if(prevCell == 0)
      if(minSum > 3 || maxSum < 3) // sum != 3
        return true;
    if(prevCell == 1)
      if(minSum > 3 || maxSum < 2) // sum not in {2, 3}
        return true;
  }
  return false;
}
// работает
function initArray(xSize, ySize, value) {
  let arr = [];
  for(let i = 0; i < xSize; i++) {
    arr[i] = new Array();
    for(let j = 0; j < ySize; j++) {
      arr[i][j] = value;
    }
  }
  return arr;
}
// работает
function init3DArray(xSize, ySize, zSize, value) {
  let arr = [];
  for(let i = 0; i < xSize; i++) {
    arr[i] = new Array();
    for(let j = 0; j < ySize; j++) {
      arr[i][j] = new Array();
      for(let k = 0; k < zSize; k++) {
        arr[i][j][k] = value;
      }
    }
  }
  return arr;
}
// исправлено
function detectErrors(arr) {
  errors = [];
  let result = false;
  let startK = zLoopBack ? 0 : 1
  for(let i = 0; i < logicSize.w; i++)
    for(let j = 0; j < logicSize.h; j++)
      for(let k = startK; k < logicSize.z; k++) {
        result = valueError(arr, i, j, k, true) || result;
      }
  return result;
}
// работает
function drawGrid(x, y, xSize, ySize, rectSize) {
  for(let i = 0; i <= xSize; i++) {
    let constX = i * rectSize + x;
    line(constX, y, constX, y + ySize * rectSize);
  }
  for(let i = 0; i <= ySize; i++) {
    let constY = i * rectSize + y;
    line(x, constY, x + xSize * rectSize, constY);
  }
}

function drawText(dx, dy, arr) {
  noStroke()
  fill(TEXT_COLOR);
  for(let i = 0; i < arr.length; i++)
    for(let j = 0; j < arr[i].length; j++)
      for(let k = 0; k < arr[i][j].length; k++) {
        text(getSymbol(arr[i][j][k]), dx + rectSize * i, dy + rectSize * j + offset.dy * k);
      }
}
 // исправлено
function drawBackground(dx, dy, offsetDY, arr) {
  // эта часть исправлена
  for(let i = 0; i < arr.length; i++)
    for(let j = 0; j < arr[i].length; j++)
      for(let k = 0; k < arr[i][j].length; k++) {
        let cell = arr[i][j][k];
        if(cell == 0) {
          fill(ZERO_COLOR);
        } else if(cell == 1) {
          fill(ONE_COLOR);
        }
        if(cell < 2)
          rect(dx + rectSize * i, dy + rectSize * j + offsetDY * k, rectSize, rectSize);
      }
  // и эта часть тоже исправлена
  fill(ERROR_COLOR);
  for(let i = 0; i < errors.length; i++) {
    let ei = errors[i].i, ej = errors[i].j, ek =  errors[i].k;
    rect(dx + rectSize * ei, dy + rectSize * ej + offsetDY * ek, rectSize, rectSize);
  }
}

function getSymbol(value) {
  if(value < listOfSymbols.length) {
    return listOfSymbols[value];
  } else {
    return value.toString();
  }
}

function copyArray(a) {
  let temp = [];
  for(let i = 0; i < a.length; i++)
    temp.push(a[i]);
  return temp;
}

function copy2dArray(a) {
  let temp = [];
  for(let i = 0; i < a.length; i++) {
    let row = [];
    for(let j = 0; j < a[i].length; j++)
      row.push(a[i][j]);
    temp.push(row);
  }
  return temp;
}
  
function copy3dArray(a) {
  let temp = [];
  for(let i = 0; i < a.length; i++) {
    let row = [];
    for(let j = 0; j < a[i].length; j++) {
        let box = [];
        for(let k = 0; k < a[i][j].length; k++) {
          box.push(a[i][j][k]);
        }
        row.push(box);
      }
    temp.push(row);
  }
  return temp;
}
// disable context menu
function logicUnion(u, s) {
  if(u == 3) {
    return s
  } else if(u == 2) {
    return u
  } else if(u == 0) {
    if(s == 0) {
      return 0
    } else if(s == 1 || s == 2) { // (0, 1) -> 2
      return 2
    } else {
      throw "s not in {0, 1, 2, 3}"
    }
  } else if(u == 1) {
    if(s == 1) {
      return 1
    } else if(s == 0 || s == 2) { // (1, 0) -> 2
      return 2
    } else {
      throw "s not in {0, 1, 2, 3}"
    }
  } else {
    throw "u not in {0, 1, 2, 3}"
  }
}

window.oncontextmenu = function() {
  return false;
}