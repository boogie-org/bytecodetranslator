﻿/*
 ******************************************************************************
 This file is part of BigWoo.NET.

    BigWoo.NET is free software; you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation; either version 2 of the License, or
    (at your option) any later version.

    BigWoo.NET is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with BigWoo.NET; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA


    architected and written by 
    matt raffel 
    matt.raffel@mindspring.com

   copyright (c) 2008 by matt raffel unless noted otherwise

 ******************************************************************************
*/
#region using statements
using System;
using System.Collections.Generic;
using System.Text;
using System.Configuration;
using System.IO;
#endregion

namespace CodeCounter.Library
{
    /// <summary>
    /// XamlCodeCounterLogic
    /// </summary>
    public class XamlCodeCounterLogic : ICodeCounterLogic
    {
        private bool _isInComment = false;

        /// <summary>
        /// Performs all the evaluations while are stepping through
        /// a multi line comment
        /// </summary>
        /// <param name="line">string</param>
        /// <returns>CodeCounterLineType</returns>
        private CodeCounterLineType EvaluateWhileInComment(string line)
        {
            if (false == string.IsNullOrEmpty(line))
            {
                if (true == line.Contains("-->"))
                {
                    _isInComment = false;

                    int endOfCommentIndex = line.IndexOf("-->");

                    endOfCommentIndex += 3;

                    if (endOfCommentIndex < line.Length)
                        return CodeCounterLineType.CodeAndComment;
                }
            }

            return CodeCounterLineType.CommentOnly;
        }

        /// <summary>
        /// Evaluates a line
        /// </summary>
        /// <param name="line">string</param>
        /// <returns>CodeCounterLineType</returns>
        private CodeCounterLineType Evaluate(string line)
        {
            if (true == line.StartsWith("<!--"))
            {
                _isInComment = true;

                // because it is possible the comment terminates
                // in this same line and to ensure that we count code after the comment
                // terminates, use our EvaluateWhileInComment to determine
                // return value
                return EvaluateWhileInComment(line);
            }

            if (true == line.Contains("<!--"))
            {
                _isInComment = true;

                // because it is possible the comment terminates
                // in this same line and to ensure that we count code after the comment
                // terminates, use our EvaluateWhileInComment to determine
                // if the comment has finished.  we will ignore its return
                // value as the only possible legal value for this case is 
                // CodeCounterLineType.CodeAndComment
                EvaluateWhileInComment(line);

                return CodeCounterLineType.CodeAndComment;
            }

            return CodeCounterLineType.Code;
        }

        #region ICodeCounterLogic Members
        /// <summary>
        /// 
        /// </summary>
        /// <param name="line"></param>
        /// <returns></returns>
        public CodeCounterLineType LineType(string line)
        {
            if (true == string.IsNullOrEmpty(line))
                return CodeCounterLineType.EmptyLine;

            string trimmed = line.Trim();

            if (true == string.IsNullOrEmpty(line))
                return CodeCounterLineType.EmptyLine;

            if (true == _isInComment)
                return EvaluateWhileInComment(trimmed);
            else
                return Evaluate(trimmed);
        }

        /// <summary>
        /// should return something like cs or vb or sql etc
        /// </summary>
        /// <returns>string[]</returns>
        public string[] FileTypesHandled()
        {
            return new string[] { "xaml" };
        }


        public bool CanProcessFile(string file)
        {
            FileInfo info = new FileInfo(file);
            string fileExtension = info.Extension.ToLower();
            if (".xaml" == fileExtension)
                return true;

            return false;
        }

        public bool EngineCanDetermineBlankLines()
        {
            return true;
        }

        public void PrefileProcessing(string fileName) { }

        public void PostfileProcessing(string fileName) { }

        #endregion
    }

}
