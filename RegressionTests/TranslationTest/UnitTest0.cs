using System;
using System.Text;
using System.Collections.Generic;
using System.Linq;
using Microsoft.VisualStudio.TestTools.UnitTesting;
using System.IO;
using Microsoft.Cci;
using Microsoft.Cci.MetadataReader;
using Microsoft.Cci.MutableCodeModel;
using Microsoft.Cci.Contracts;
using Microsoft.Cci.ILToCodeModel;
using BytecodeTranslator;

namespace TranslationTest {
  /// <summary>
  /// Summary description for UnitTest0
  /// </summary>
  [TestClass]
  public class UnitTest0 {
    public UnitTest0() {
      //
      // TODO: Add constructor logic here
      //
    }

    private TestContext testContextInstance;

    /// <summary>
    ///Gets or sets the test context which provides
    ///information about and functionality for the current test run.
    ///</summary>
    public TestContext TestContext {
      get {
        return testContextInstance;
      }
      set {
        testContextInstance = value;
      }
    }

    private string InputAssemblyPath =>
      typeof(RegressionTestInput.Class0).Assembly.Location;

    #region Additional test attributes
    //
    // You can use the following additional attributes as you write your tests:
    //
    // Use ClassInitialize to run code before running the first test in the class
    // [ClassInitialize()]
    // public static void MyClassInitialize(TestContext testContext) { }
    //
    // Use ClassCleanup to run code after all tests in a class have run
    // [ClassCleanup()]
    // public static void MyClassCleanup() { }
    //
    // Use TestInitialize to run code before running each test 
    // [TestInitialize()]
    // public void MyTestInitialize() { }
    //
    // Use TestCleanup to run code after each test has run
    // [TestCleanup()]
    // public void MyTestCleanup() { }
    //
    #endregion

    private string ExecuteTest(string assemblyName, HeapFactory heapFactory) {
      var options = new Options();
      options.monotonicHeap = true;
      options.dereference = Options.Dereference.Assume;
      return BCT.TranslateAssemblyAndReturnOutput(new List<string> { assemblyName }, heapFactory, options, null, false);
    }

    private void ComparisonTest(string name, Heap heap)
    {
      Stream resource = typeof(UnitTest0).Assembly.GetManifestResourceStream(
        "TranslationTest." + name + "Input.txt");
      StreamReader reader = new StreamReader(resource);
      string expected = reader.ReadToEnd();
      var result = ExecuteTest(InputAssemblyPath, new SplitFieldsHeap());
      if (result != expected)
      {
        string resultFile = Path.Combine(TestContext.DeploymentDirectory, name + "Output.txt");
        File.WriteAllText(resultFile, result);
        var msg = String.Format("Output didn't match: {0}Input.txt \"{1}\"", name, resultFile);
        Assert.Fail(msg);
      }
    }

    [TestMethod]
    public void SplitFieldsHeap() {
      ComparisonTest("SplitFieldsHeap", new SplitFieldsHeap());
    }

    [TestMethod]
    public void GeneralHeap() {
      ComparisonTest("GeneralHeap", new GeneralHeap());
    }

  }
}
 