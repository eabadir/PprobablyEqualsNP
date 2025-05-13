const filePaths = [
  //Readme files
  { path: "./temp/include/", includeFile: true, outputFile: "pkg.txt" },

];
const fs = require('fs');
const path = require('path');
const readline = require('readline');

// Create readline interface for user input
const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout
});

// Function to read file content and create an object with path and text
const readFileContent = (filePathObj) => {
  // Skip files where includeFile is false
  if (!filePathObj.includeFile) {
    return null;
  }

  const absolutePath = path.resolve(__dirname, filePathObj.path);
  
  // Check if the path is a directory
  try {
    const stat = fs.statSync(absolutePath);
    if (stat.isDirectory()) {
      // This is a directory, so we'll process all files in it
      console.log(`Reading directory: ${filePathObj.path}`);
      return null; // Return null here, directory contents will be processed separately
    }
  } catch (error) {
    console.error(`Error accessing path ${filePathObj.path}:`, error.message);
    return {
      path: filePathObj.path,
      text: null,
      error: error.message,
      outputFile: filePathObj.outputFile
    };
  }

  // Process regular file
  try {
    const content = fs.readFileSync(absolutePath, 'utf8');
    console.log(`Reading file: ${filePathObj.path}`);
    return {
      path: filePathObj.path,
      text: content,
      outputFile: filePathObj.outputFile
    };
  } catch (error) {
    console.error(`Error reading file ${filePathObj.path}:`, error.message);
    return {
      path: filePathObj.path,
      text: null,
      error: error.message,
      outputFile: filePathObj.outputFile
    };
  }
};

// Function to ensure directory exists
const ensureDirectoryExists = (dirPath) => {
  if (!fs.existsSync(dirPath)) {
    fs.mkdirSync(dirPath, { recursive: true });
    console.log(`Created directory: ${dirPath}`);
  }
};

// Function to load manifest file
const loadManifestFile = (manifestPath) => {
  try {
    const absolutePath = path.resolve(__dirname, manifestPath);
    const manifestData = JSON.parse(fs.readFileSync(absolutePath, 'utf8'));
    console.log(`Loaded manifest from: ${manifestPath}`);
    return manifestData.files || [];
  } catch (error) {
    console.error(`Error loading manifest file ${manifestPath}:`, error.message);
    return null;
  }
};

// Function to ask a yes/no question
const askYesNo = async (question) => {
  return new Promise((resolve) => {
    rl.question(`${question} (y/n): `, (answer) => {
      resolve(answer.toLowerCase() === 'y' || answer.toLowerCase() === 'yes');
    });
  });
};

// Function to ask for output file name
const askForOutputFile = async (defaultOutput = 'output.json',relativePath) => {
  return new Promise((resolve) => {
    let question = `Enter output JSON file name (default: ${defaultOutput}): `;
    if (relativePath) {
      question = `Enter output JSON file name for folder "${relativePath}" (default: ${defaultOutput}): `;
    }
    rl.question(question, (answer) => {
      resolve(answer.trim() || defaultOutput);
    });
  });
};

// Function to recursively walk a directory and collect files
const walkDirectory = async (dirPath, basePath, isInteractive, defaultOutputFile = 'output.json') => {
  const files = fs.readdirSync(dirPath);
  let collectedFiles = [];
  
  for (const file of files) {
    const fullPath = path.join(dirPath, file);
    const relativePath = path.join(basePath, file);
    const stat = fs.statSync(fullPath);
    
    if (stat.isDirectory()) {
      if (isInteractive) {
        console.log(`\nFound directory: "${relativePath}"`);
        const includeDir = await askYesNo(`Include directory "${relativePath}"?`);
        if (!includeDir) continue;
        
        // Ask whether to package all files in this directory branch or continue interactively
        const packageAll = await askYesNo(`Do you want to package all files in "${relativePath}" automatically (y) or continue interactively (n)?`);
        
        const subdirFiles = await walkDirectory(
          fullPath,
          relativePath,
          !packageAll, // If packageAll is true, we set interactive to false for subdirectories
          defaultOutputFile
        );
        collectedFiles = collectedFiles.concat(subdirFiles);
      } else {
        // Non-interactive mode: include all files in subdirectories
        const subdirFiles = await walkDirectory(
          fullPath,
          relativePath,
          false,
          defaultOutputFile
        );
        collectedFiles = collectedFiles.concat(subdirFiles);
      }
    } else {
      // It's a file
      let includeFile = true;
      let outputFile = defaultOutputFile;
      
      if (isInteractive) {
        includeFile = await askYesNo(`Include file "${relativePath}"?`);
        // if (includeFile) {
        //   outputFile = await askForOutputFile(defaultOutputFile, relativePath);
        // }
      }
      
      if (includeFile) {
        collectedFiles.push({
          path: `./${relativePath}`,
          includeFile: true,
          outputFile: outputFile
        });
      }
    }
  }
  
  return collectedFiles;
};

// Function to handle interactive file selection
const interactiveFileSelection = async () => {
  console.log("\n=== Interactive Mode ===");
  console.log("You'll be prompted to select files and folders to include in the manifest.\n");
  
  return new Promise(async (resolve) => {
    rl.question('Enter the base folder path (relative to the script): ', async (baseFolder) => {
      const basePath = baseFolder.trim() || '.';
      const fullPath = path.resolve(__dirname, basePath);
      
      if (!fs.existsSync(fullPath)) {
        console.error(`Error: Directory ${basePath} does not exist`);
        resolve([]);
        return;
      }
      
      //const defaultOutputFile = await askForOutputFile();
      const defaultOutputFile = 'output.json';
      const files = await walkDirectory(fullPath, '', true, defaultOutputFile);
      
      console.log(`\nSelected ${files.length} files for the manifest.`);
      
      // Ask where to save the manifest file
      rl.question('Enter the manifest file name to save (default: new_manifest.json): ', (manifestFileName) => {
        const fileName = manifestFileName.trim() || 'new_manifest.json';
        const manifestPath = path.join(__dirname, 'temp', fileName);
        
        // Ensure the directory exists
        ensureDirectoryExists(path.dirname(manifestPath));
        
        // Create manifest content
        const manifestContent = {
          timestamp: new Date().toISOString(),
          files: files.map(({ path, includeFile, outputFile }) => ({
            path,
            includeFile,
            outputFile
          }))
        };
        
        // Save manifest file
        fs.writeFileSync(manifestPath, JSON.stringify(manifestContent, null, 2));
        console.log(`\nManifest saved to: ${manifestPath}`);
        console.log('You can now use this manifest file with option 1 to package the files.');
        
        resolve([]);  // Return empty array to avoid packaging in this mode
      });
    });
  });
};

// Group files by their output file and write to specified output directory
const createOutputFilesWithPaths = (pathsConfig, outputDir = '', inputManifestPath = '') => {
  // Create a map of excluded files
  const excludedPaths = new Map();
  pathsConfig.forEach(item => {
    if (!item.includeFile) {
      // Store the absolute path for easier comparison later
      excludedPaths.set(path.resolve(__dirname, item.path), item.outputFile);
    }
  });
  
  // Process directory entries and expand them into individual files
  let expandedPaths = [];
  pathsConfig.forEach(item => {
    if (item.includeFile) {
      const absolutePath = path.resolve(__dirname, item.path);
      try {
        const stat = fs.statSync(absolutePath);
        if (stat.isDirectory()) {
          // This is a directory, so add all non-excluded files from it
          const directoryFiles = processDirectory(absolutePath, item.path, item.outputFile, excludedPaths);
          expandedPaths = expandedPaths.concat(directoryFiles);
        } else {
          // This is a regular file
          expandedPaths.push(item);
        }
      } catch (error) {
        console.error(`Error processing path ${item.path}:`, error.message);
        expandedPaths.push(item); // Keep the original entry in case it's a yet-to-be-created file
      }
    }
  });
  
  // Read all file contents from the expanded list
  const fileContents = expandedPaths
    .map(readFileContent)
    .filter(content => content !== null);

  // Group by output file
  const groupedFiles = {};
  fileContents.forEach(file => {
    if (!groupedFiles[file.outputFile]) {
      groupedFiles[file.outputFile] = [];
    }
    // Remove the outputFile property before adding to the group
    const { outputFile, ...fileData } = file;
    groupedFiles[file.outputFile].push(fileData);
  });

  // Create output directory if specified
  let baseDir = path.resolve(__dirname);
  baseDir = path.join(baseDir, 'temp');
  const targetDir = outputDir ? path.join(baseDir, outputDir) : baseDir;

  if (outputDir) {
    ensureDirectoryExists(targetDir);
  }

  // Write each group to its own file in the target directory
  Object.entries(groupedFiles).forEach(([outputFile, files]) => {
    const concatenatedContent = files.map(file => {
      const delimiter = `// ---------- [${file.path}] ----------\n`;
      return `${delimiter}${file.text}`;
    }).join('\n\n'); // Add spacing between files

    const outputPath = path.join(targetDir, outputFile);
    fs.writeFileSync(outputPath, concatenatedContent);
    console.log(`Output saved to: ${outputPath}`);
  });

  // Create manifest.json with the filePaths configuration
  const manifestContent = {
    timestamp: new Date().toISOString(),
    files: pathsConfig
      .map(({ path, includeFile, outputFile }) => ({
        path,
        includeFile,
        outputFile
      }))
  };

  const manifestPath = path.join(targetDir, 'manifest.json');

  // Check if the manifest being written is the same as the one being read
  if (inputManifestPath && path.resolve(inputManifestPath) === manifestPath) {
    console.log('Skipping manifest write as it matches the input manifest.');
    return;
  }

  fs.writeFileSync(manifestPath, JSON.stringify(manifestContent, null, 2));
  console.log(`Manifest saved to: ${manifestPath}`);
};

// Function to process a directory and return all file paths
const processDirectory = (absoluteDirPath, relativeDirPath, outputFile, excludedPaths) => {
  const result = [];
  
  try { 
    const files = fs.readdirSync(absoluteDirPath);
    
    for (const file of files) {
      const absoluteFilePath = path.join(absoluteDirPath, file);
      const relativeFilePath = path.join(relativeDirPath, file);
      
      // Check if this file is in the excluded paths
      if (excludedPaths.has(absoluteFilePath)) {
        console.log(`Skipping excluded file: ${relativeFilePath}`);
        continue;
      }
      
      const stat = fs.statSync(absoluteFilePath);
      
      if (stat.isDirectory()) {
        // Recursively process subdirectories
        const subDirFiles = processDirectory(absoluteFilePath, relativeFilePath, outputFile, excludedPaths);
        result.push(...subDirFiles);
      } else {
        // Add the file to the result
        result.push({
          path: `./${relativeFilePath}`,
          includeFile: true,
          outputFile: outputFile
        });
      }
    }
  } catch (error) {
    console.error(`Error reading directory ${relativeDirPath}:`, error.message);
  }
  
  return result;
};

// Main function to handle the file packaging process
const runFilePackager = () => {
  console.log('\n=== File Packager ===');
  console.log('1: Use manifest file - Load file paths from a saved manifest');
  console.log('2: Use default configuration - Package files using hardcoded paths');
  console.log('3: Interactive mode - Create a new manifest file by browsing directories');
  console.log('4: Use manifest and package - Create manifest AND package files in one step');
  
  rl.question('Select mode (1-4): ', async (mode) => {
    let pathsToUse = filePaths;
    let inputManifestPath = '';

    if (mode === '1') {
      rl.question('Enter a manifest file path to use: ', (manifestPath) => {
        if (manifestPath.trim()) {
          const loadedPaths = loadManifestFile(manifestPath.trim());
          if (loadedPaths) {
            pathsToUse = loadedPaths;
            inputManifestPath = manifestPath.trim();
            askOutputAndProcess(pathsToUse, inputManifestPath);
          } else {
            console.log('Error loading manifest. Exiting...');
            rl.close();
          }
        } else {
          console.log('No manifest path provided. Exiting...');
          rl.close();
        }
      });
    } else if (mode === '3') {
      // Interactive mode - only create manifest
      await interactiveFileSelection();
      console.log('\nManifest creation complete. Run the tool again with option 1 to package files.');
      rl.close();
    } else if (mode === '4') {
      // Interactive mode + packaging
      const selectedFiles = await interactiveFileSelection();
      if (selectedFiles && selectedFiles.length > 0) {
        askOutputAndProcess(selectedFiles, inputManifestPath);
      } else {
        console.log('\nNo files selected or manifest already saved. Exiting...');
        rl.close();
      }
    } else {
      // Default mode (2)
      console.log('Using default file paths configuration.');
      askOutputAndProcess(pathsToUse, inputManifestPath);
    }
  });
};

// Helper function to ask for output directory and process files
const askOutputAndProcess = (pathsToUse, inputManifestPath) => {
  if (!pathsToUse || pathsToUse.length === 0) {
    console.log('No files to package. Exiting...');
    rl.close();
    return;
  }
  
  rl.question('Enter output folder name (leave empty for current directory): ', (outputDir) => {
    console.log(`\nPackaging ${pathsToUse.length} files...`);
    // Generate output JSON files using the selected file paths
    createOutputFilesWithPaths(pathsToUse, outputDir.trim(), inputManifestPath);
    rl.close();
  });
};

// Start the file packager
runFilePackager();